-- {-# OPTIONS_GHC -fplugin AccPlugin.AccTransform #-}

{-# LANGUAGE Strict                 #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeApplications       #-}

-- NOTE: To run with hermit script:
--    hermit Mandelbrot.hs +Main AccTransform.hss

-- TODO:
--  1) Transform boolean expressions (probably will need to be done in
--  a plugin/HERMIT).
--
--  2) Transform recursion to 'while' (definitely will need to be done in
--  a plugin/HERMIT).

import           Prelude hiding (abs, not)

import           Codec.Picture

import           Data.Array.Accelerate hiding (fromIntegral, uncurry)
import qualified Data.Array.Accelerate as A
import           Data.Array.Accelerate.Interpreter (run)

import           GHC.Exts

-- Accelerate transformation: --
import           AccPlugin.WW
import           Data.Function (fix)

maxIterations :: Float
maxIterations = 100

width, height :: Int
width  = 800
height = 600

-- Scale x to [-2.5, 1] and y to [-1, 1]
scaleX, scaleY :: Floating a => a -> a
scaleX x = -2.5 + x * ((2.5 + 1) / fromIntegral width)
scaleY y = -1 + y * ((1 + 1) / fromIntegral height)

-- NOTE: The Ord instances for Exp types are a bit of a lie (w.r.t. all the
-- comparison operations).
pointColor :: Int -> Int -> (Float, Float, Float)
pointColor origX origY = go (0, 0, 0)
  where
    (scaledX, scaledY) = (scaleX $ fromIntegral origX, scaleY $ fromIntegral origY)

    go :: (Float, Float, Float) -> (Float, Float, Float)
    go (n, x, y)
      | n >= maxIterations = (0, 0, 1)
      | x*x + y*y >= 4     = ((n/maxIterations), 0, 0)
      | otherwise          = go ((n+1)
                                ,(x*x - y*y + scaledX)
                                ,(2*x*y + scaledY)
                                )
{-# NOINLINE pointColor #-}

toRGBF :: (a -> a -> (Float, Float, Float)) -> a -> a -> PixelRGBF
toRGBF f x y =
    let (r, g, b) = f x y
    in PixelRGBF r g b
{-# NOINLINE toRGBF #-}

-- | This is used to avoid infinite inlining in a RULE
toRGBF' :: (a -> a -> (Float, Float, Float)) -> a -> a -> PixelRGBF
toRGBF' = toRGBF
{-# NOINLINE toRGBF' #-}

main :: IO ()
main = do
  let image = generateImage (toRGBF pointColor) width height
  savePngImage "mandelbrot.png" (ImageRGBF image)


-- Accelerate transformation --
indexing2 :: (Exp Int -> Exp Int -> Exp (Float, Float, Float))
            -> (Exp DIM2 -> Exp (Float, Float, Float))
indexing2 f dim2 = (f :: Exp Int -> Exp Int -> Exp (Float, Float, Float)) (A.fst ix) (A.snd ix)
  where
    ix :: Exp (Int, Int)
    ix = unindex2 dim2

genRGBF :: (Int -> Int -> PixelRGBF) -> Int -> Int -> Image PixelRGBF
genRGBF = generateImage

genIntermediate :: PixelRGBF -> (Float, Float, Float)
genIntermediate (PixelRGBF r g b) = (r, g, b)

interpretResult :: Array DIM2 (Float, Float, Float) -> Int -> Int -> PixelRGBF
interpretResult pixels x y =
    let (r, g, b) = indexArray pixels (Z :. x :. y)
    in
    PixelRGBF r g b


-- recCall :: a -> a
recCall :: Exp (Float, Float, Float) -> Exp (Float, Float, Float)
recCall = error "recCall: This should not be in generated code"
{-# NOINLINE recCall #-}

-- | Try to prevent a lambda from beta reducing too far
intros :: a -> a
intros = id
{-# NOINLINE intros #-}

-- | A placeholder
whileCond :: a -> Exp Bool
whileCond = error "Internal error: whileCond"


dummyX, dummyY :: Exp Int
dummyX = error "Internal error: dummyX"
dummyY = error "Internal error: dummyY"

const2 :: b -> a -> a -> b
const2 b _ _ = b
-- {-# NOINLINE const2 #-}

-- | This RULE starts the whole process.
{-# RULES "abs-intro" [~]
    toRGBF pointColor
      =
    toRGBF (const2 (rep (abs (pointColor (rep dummyX) (rep dummyY)))))
  #-}

{-# RULES "finish" [~]
    forall (f :: Exp Int -> Exp Int -> Exp (Float, Float, Float)).
    toRGBF (const2 (rep (f dummyX dummyY)))
      =
    interpretResult (run (generate (constant (Z :. width :. height)) (indexing2 f)))
  #-}

{-# RULES "abs-elim-float-scaleX" [~]
    forall (x :: Exp Int).
    abs (scaleX (fromIntegral (rep x)))
      =
    (scaleX . fromIntegral :: Exp Int -> Exp Float) x
  #-}

{-# RULES "abs-elim-float-scaleY" [~]
    forall (y :: Exp Int).
    abs (scaleY (fromIntegral (rep y)))
      =
    (scaleY . fromIntegral :: Exp Int -> Exp Float) y
  #-}


{-# RULES "fix-abs-rep-intro" [~]
    forall f (a :: (Float, Float, Float)).
    abs (fix f a)
      =
    (fix (\fRec -> intros (\x -> abs (f (rep . fRec) x)))) a
  #-}

{-# RULES "recCall-triple-rep-float" [~]
    forall (x :: Exp Float) (y :: Exp Float) (z :: Exp Float).
    recCall (abs (rep x, rep y, rep z))
      =
    recCall (lift (x, y, z))
  #-}

-- {-# RULES "abs-plainRep-elim" [~]
--     forall (x :: Lift Exp a => a).
--     abs (plainRep x)
--       =
--     lift x
--   #-}

-- {-# RULES "recCall-plainRep" [~]
--     forall (x :: (Exp Float, Exp Float, Exp Float)).
--     recCall (plainRep x)
--       =
--     liftTriple (recCall x)
--   #-}


-- | Mark something as recursive
recursive :: a -> a
recursive = error "Internal error: 'recursive' called"

{-# RULES "recCall-intro" [~]
    forall (f :: ((Float, Float, Float) -> Exp (Float, Float, Float)) -> (Float, Float, Float) -> Exp (Float, Float, Float)) arg.
    fix f arg
      =
    recursive (f (\x -> recCall (abs x)) arg)
  #-}

{-# RULES "while-intro" [~]
    forall f (x :: (Float, Float, Float)).
    recursive (intros f x)
      =
    while whileCond (\z -> f (rep z)) (abs x)
  #-}


efirst, esecond, ethird :: (a, a, a) -> a
efirst  (a, _, _) = a
esecond (_, b, _) = b
ethird  (_, _, c) = c

{-# RULES "triple-rep" [~]
    forall (x :: Exp (Float, Float, Float)).
    rep x
      =
    (efirst (rep x), esecond (rep x), ethird (rep x))
  #-}

{-# RULES "efirst-float-in" [~]
    forall (x :: Exp (Float, Float, Float)).
    abs (efirst (rep x))
      =
    efirst (unlift x)
  #-}

{-# RULES "abs-float-triple" [~]
    forall (x :: Float) (y :: Float) (z :: Float).
    abs (x, y, z)
      =
    lift (abs x, abs y, abs z)
  #-}

{-# RULES "esecond-float-in" [~]
    forall (x :: Exp (Float, Float, Float)).
    abs (esecond (rep x))
      =
    esecond (unlift x)
  #-}

{-# RULES "ethird-float-in" [~]
    forall (x :: Exp (Float, Float, Float)).
    abs (ethird (rep x))
      =
    ethird (unlift x)
  #-}

-- Accelerate transformation RULES --
{-# RULES ">=*-intro" [~]
    forall (x :: Float) (y :: Float).
    x >= y
      =
    (rep ((abs x) >=* (abs y)) :: Bool)
  #-}

{-# RULES "+-intro" [~]
    forall (x :: Float) y.
    x + y
      =
    rep (abs x + abs y)
  #-}


{-# RULES "*-intro" [~]
    forall (x :: Float) y.
    x * y
      =
    rep (abs x * abs y)
  #-}

{-# RULES "--intro" [~]
    forall (x :: Float) y.
    x - y
      =
    rep (abs x - abs y)
  #-}

{-# RULES "/-intro"
    forall (x :: Float) y.
    x / y
      =
    rep (abs x / abs y)
  #-}

{-# RULES "abs-if->cond" [~]
    forall (b :: Bool) (t :: (Float, Float, Float)) f.
    abs (case b of True -> t; False -> f)
      =
    cond (abs b) (abs t) (abs f)
  #-}


{-# RULES "recCall-elim" [~]
    forall x.
    recCall x
      =
    x
  #-}



{-# RULES "abs/let-float" [~]
    forall x v.
    abs (let bnd = v in x)
      =
    let bnd = v
    in
    abs x
  #-}

{-# RULES "abs-rep-elim" [~]
    forall x.
    abs (rep x) = x
  #-}

-- NOTE: The general 'case' seems to be impossible with a rewrite rule:
-- NOTE: This looks like it's not safe to use unless you inline the case
-- scrutinee first, because it tries to rename the 'wild' to 'a' for some
-- reason.
{-# RULES "abs/case-float-one" [~]
    forall d x.
    abs (case d of a -> x)
      =
    case d of
      a -> abs x
  #-}


{-# RULES "abs/case-float-pair" [~]
    forall d x.
    abs (case d of (,) _ _ -> x)
      =
    case d of
      (,) _ _ -> abs x
  #-}

recCondF :: Elt t => (Exp t -> Exp Bool) -> Exp Bool -> Exp t -> Exp t -> Exp t
recCondF _ = cond
{-# NOINLINE recCondF #-}

recCondT :: Elt t => (Exp t -> Exp Bool) -> Exp Bool -> Exp t -> Exp t -> Exp t
recCondT _ = cond
{-# NOINLINE recCondT #-}

condBool :: Exp Bool -> Exp Bool
condBool = id
{-# NOINLINE condBool #-}

cond' :: Elt t => Exp Bool -> Exp t -> Exp t -> Exp t
cond' = cond
{-# NOINLINE cond' #-}

-- Used to find 'cond' conditions
{-# RULES "condBool-intro" [~]
    forall c t f.
    cond c t f = cond' (condBool c) t f
  #-}

-- 'condBool' calls should be eliminated before this is used
{-# RULES "cond'->cond" [~]
    forall c t f.
    cond' c t f = cond c t f
  #-}

{-# RULES "condBool-elim" [~]
    forall c.
    condBool c
      =
    c
  #-}


{-# RULES "cond-float-else" [~]
    forall c x t f.
    cond (c x) t (recCall f)
      =
    recCondF (not . c) (c x) t (recCall f)
  #-}

{-# RULES "recCondF-float-else" [~]
    forall c x accCond c' t t' f'.
    cond (c x) t (recCondF accCond c' t' f')
      =
    recCondF ((&&*) <$> (not . c) <*> accCond) (c x) t (recCondF accCond c' t' f')
  #-}

dummyArg :: a
dummyArg = error "Internal error: dummyArg"
{-# NOINLINE dummyArg #-}

grabbedCond :: a -> b -> a
grabbedCond = const
{-# NOINLINE grabbedCond #-}


{-# RULES "dummyArg-intro" [~]
    forall fn i.
    while whileCond fn i
      =
    while whileCond (grabbedCond fn (fn dummyArg)) i
  #-}

{-# RULES "grab-cond" [~]
    forall fn c c' t f i.
    while whileCond (grabbedCond fn (recCondF c c' t f)) i
      =
    while c fn i
  #-}

-- NOTE: This will probably have to be implemented in the plugin.
-- {-# RULES "rep-if"
--     forall b (t :: Elt (Plain a) => a) f.
--     if (rep b) then t else f
--       =
--     cond b t f
--   #-}


-- {-# RULES "abs-rep=id/let"
--     forall x v.
--     abs (let bnd = v in rep x)
--       =
--     let bnd = v
--     in x
--   #-}

