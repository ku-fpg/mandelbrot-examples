-- {-# OPTIONS_GHC -fplugin AccTransform #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

import           Codec.Picture

import           Data.Array.Accelerate hiding (fromIntegral, uncurry)
import qualified Data.Array.Accelerate as A
import           Data.Array.Accelerate.Interpreter (run)

maxIterations :: Integral a => a
maxIterations = 100

width, height :: Int
width  = 800
height = 600

-- Scale x to [-2.5, 1] and y to [-1, 1]
scaleX, scaleY :: Floating a => a -> a
scaleX x = -2.5 + x * ((2.5 + 1) / fromIntegral width)
scaleY y = -1 + y * ((1 + 1) / fromIntegral height)

class NumericConv a b | a -> b where
    conv :: a -> b

instance NumericConv Int Float where
    conv = fromIntegral

instance NumericConv (Exp Int) (Exp Float) where
    conv = A.fromIntegral

pointColor :: forall a b. (NumericConv a b, Integral a, Floating b, Ord b) =>
                a -> a -> (b, b, b)
pointColor origX' origY' = go 0 0 0
  where
    origX, origY :: b
    origX = conv origX'
    origY = conv origY'

    scaledX, scaledY :: b
    (scaledX, scaledY) = (scaleX origX, scaleY origY)

    go :: Int -> b -> b -> (b, b, b)
    go n x y
      | n >= maxIterations = (0, 0, 1)
      | x^2 + y^2 >= 4     = ((fromIntegral n/fromIntegral maxIterations), 0, 0)
      | otherwise          = go (n+1)
                                (x^2 - y^2 + scaledX)
                                (2*x*y + scaledY)
{-# NOINLINE pointColor #-}

toRGBF :: (a -> a -> (Float, Float, Float)) -> a -> a -> PixelRGBF
toRGBF f x y =
    let (r, g, b) = f x y
    in PixelRGBF r g b
{-# NOINLINE toRGBF #-}

main :: IO ()
main = do
  let image = generateImage (toRGBF pointColor) width height
  savePngImage "mandelbrot.png" (ImageRGBF image)


-- Accelerate transformation --
indexing2 :: (forall a b. (Floating b, Ord b, NumericConv a b, Integral a) =>
                          a -> a -> (b, b, b))
              -> (Exp DIM2 -> Exp (Float, Float, Float))
indexing2 f dim2 = lift $ f (A.fst ix) (A.snd ix)
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

{-# RULES
      "generateImage->Acc"
      forall (f :: forall a b. (NumericConv a b, Integral a, Floating b, Ord b) => a -> a -> (b, b, b)) w h.
      generateImage (toRGBF f) w h
        =
      genRGBF (interpretResult (run (generate
                            (constant
                              (Z :. width :. height))
                            (indexing2 f))))
                    w
                    h
  #-}

-- {-# RULES "fromIntegral->A.fromIntegral"
--       forall (n :: (Elt a, IsIntegral a, Integral a) => Exp a).
--       fromIntegral n = A.fromIntegral (lift n)
--   #-}

