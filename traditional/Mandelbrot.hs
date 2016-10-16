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

import           Prelude hiding (abs)

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
scaleX, scaleY :: Float -> Float
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
indexing2 :: (Exp Int -> Exp Int -> (Exp Float, Exp Float, Exp Float))
            -> (Exp DIM2 -> Exp (Float, Float, Float))
indexing2 f dim2 = lift $ (f :: Exp Int -> Exp Int -> (Exp Float, Exp Float, Exp Float)) (A.fst ix) (A.snd ix)
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


recCall :: a -> Plain a
recCall = error "recCall: This should not be in generated code"
{-# NOINLINE recCall #-}

-- | Try to prevent a lambda from beta reducing too far
intros :: a -> a
intros = id
{-# NOINLINE intros #-}

-- | A placeholder
whileCond :: a -> Exp Bool
whileCond = error "Internal error: whileCond"


-- | This RULE starts the whole process.
{-# RULES "abs-intro" [~]
    toRGBF pointColor
      =
    toRGBF (\startX startY -> rep (abs (inline pointColor startX startY)))
  #-}

{-# RULES "fix-abs-rep-intro" [~]
    forall f (a :: (Float, Float, Float)).
    abs (fix f a)
      =
    (fix (\fRec -> intros (\x -> abs (f (rep . fRec) x)))) a
  #-}

-- {-# RULES "abs-recCall-elim" [~]
--     forall (x :: (Exp Float, Exp Float, Exp Float)).
--     abs (recCall x)
--       =
--     liftTriple x
--   #-}

{-# RULES "recCall-triple-rep-float" [~]
    forall (x :: Exp Float) (y :: Exp Float) (z :: Exp Float).
    recCall (abs (rep x, rep y, rep z))
      =
    recCall (x, y, z)
  #-}

{-# RULES "recCall->plainRep" [~]
    forall (x :: (Exp Float, Exp Float, Exp Float)).
    recCall x
      =
    plainRep x
  #-}

{-# RULES "abs-plainRep-elim" [~]
    forall (x :: Lift Exp a => a).
    abs (plainRep x)
      =
    lift x
  #-}

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
    recursive (f (\x -> abs (recCall (abs x))) arg)
  #-}

-- {-# RULES "while-intro" [~]
--     forall (f :: (Float, Float, Float) -> (Exp Float, Exp Float, Exp Float))
--            x.
--     rep (lift (recursive (intros f)) (lift x))
--       =
--     while whileCond (undefined . f . rep) undefined
--   #-}

-- {-# RULES "app-separate" [~]
--     forall f (x :: (Float, Float, Float)).
--     lift (recursive (intros (f x)))
--       =
--     _ (recursive f) (lift x)
--   #-}

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

{-# RULES "abs-if->cond" [~]
    forall (b :: Bool) (t :: (Float, Float, Float)) f.
    abs (case b of True -> t; False -> f)
      =
    cond (abs b) (abs t) (abs f)
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

