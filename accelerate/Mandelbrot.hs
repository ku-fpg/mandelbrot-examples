{-# LANGUAGE Strict #-}

import           Prelude hiding (zipWith, map, fst, snd, (<*), fromIntegral)
import qualified Prelude as P

import           Data.Complex

import           Data.Array.Accelerate
import qualified Data.Array.Accelerate as A
import           Data.Array.Accelerate.Interpreter

import           Codec.Picture

maxIterations :: Int
maxIterations = 100

width, height :: Int
width  = 800
height = 600

-- Scale x to [-2.5, 1] and y to [-1, 1]
scaleX, scaleY :: Exp Float -> Exp Float
scaleX x = -2.5 + x * ((2.5 + 1) / P.fromIntegral width)
scaleY y = -1 + y * ((1 + 1) / P.fromIntegral height)

mandelbrot :: Acc (Array DIM2 Int)
mandelbrot = generate (constant (Z :. width :. height)) go --map go initArray
  where
    getX, getY :: (Exp Int, Exp Float, Exp Float) -> Exp Float
    getX (_, x, _) = x
    getY (_, _, y) = y

    getIter :: (Exp Int, Exp Float, Exp Float) -> Exp Int
    getIter (i, _, _) = i

    go :: Exp DIM2 -> Exp Int
    go init' =
      lift1 getIter $ while continueCond
                      (lift1 step)
                      (lift (0 :: Int, 0.0 :: Float, 0.0 :: Float))
      where
        step :: (Exp Int, Exp Float, Exp Float) -> (Exp Int, Exp Float, Exp Float)
        step (i, x, y) = (i+1
                         ,(x^2 - y^2 + scaledX)
                         ,(2*x*y + scaledY))

        init = unindex2 init'

        scaledX, scaledY :: Exp Float
        (scaledX, scaledY) =
          (scaleX $ fromIntegral (fst init :: Exp Int), scaleY $ fromIntegral (snd init :: Exp Int))

    continueCond :: Exp (Int, Float, Float) -> Exp Bool
    continueCond e =
      (lift1 getIter e <* lift maxIterations) &&* ((lift1 getX e^2 + lift1 getY e^2) <* 4)

pixelColor :: Array DIM2 Int -> Int -> Int -> PixelRGBF
pixelColor pixels x y
  | iters >= maxIterations = PixelRGBF 0 0 1
  | otherwise              = PixelRGBF (P.fromIntegral iters / P.fromIntegral maxIterations) 0 0
  where
    iters = indexArray pixels (Z :. x :. y)


main :: IO ()
main = do
  let pixels = run mandelbrot
      image  = generateImage (pixelColor pixels) width height
  savePngImage "mandelbrot.png" (ImageRGBF image)

