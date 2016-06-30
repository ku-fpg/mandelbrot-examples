{-# LANGUAGE Strict #-}

import           Prelude hiding (zipWith, map, fst, snd, (<*))

import           Data.Array.Accelerate hiding (fromIntegral)
import qualified Data.Array.Accelerate as A
import           Data.Array.Accelerate.Interpreter

import           Codec.Picture

import Debug.Trace

maxIterations :: Int
maxIterations = 1000

width, height :: Int
width  = 800
height = 600

-- Scale x to [-2.5, 1] and y to [-1, 1]
scaleX, scaleY :: Exp Float -> Exp Float
scaleX', scaleY' :: Float -> Float
scaleX x = -2.5 + x * ((2.5 + 1) / fromIntegral width)
scaleY y = -1 + y * ((1 + 1) / fromIntegral height)
scaleX' x = -2.5 + x * ((2.5 + 1) / fromIntegral width)
scaleY' y = -1 + y * ((1 + 1) / fromIntegral height)

mandelbrot :: Acc (Array DIM2 Int)
mandelbrot = map go initArray
  where
    initArray :: Acc (Array DIM2 (Int, (Float, Float)))
    initArray = lift $ fromList (Z :. width :. height) initList

    initList :: [(Int, (Float, Float))]
    initList =
      [(0, (scaleX' x, scaleY' y))
      | x <- [0..fromIntegral width]
      , y <- [0..fromIntegral height]
      ]

    getX, getY :: Exp (Int, (Float, Float)) -> Exp Float
    getX = fst . snd
    getY = snd . snd

    getIters :: Exp (Int, (Float, Float)) -> Exp Int
    getIters = fst

    go :: Exp (Int, (Float, Float)) -> Exp Int
    go init =
      getIters $ while continueCond
                       (\e ->
                           (lift (getIters e + 1
                                 ,(getX e^2 - getY e^2 + scaledX
                                  ,2*getX e*getY e + scaledY))))
                       init
      where
        scaledX, scaledY :: Exp Float
        (scaledX, scaledY) = (scaleX (getX init), scaleY (getY init))

    continueCond :: Exp (Int, (Float, Float)) -> Exp Bool
    continueCond e =
      (fst e <* lift maxIterations &&* getX e^2 + getY e^2 <* 4)

pixelColor :: Array DIM2 Int -> Int -> Int -> PixelRGBF
pixelColor pixels x y
  | iters >= maxIterations = PixelRGBF 0 0 1
  | otherwise              = traceShow iters $ PixelRGBF (fromIntegral iters / fromIntegral 5) 0 0
  where
    iters = indexArray pixels (Z :. x :. y)


main :: IO ()
main = do
  let pixels = run mandelbrot
      image  = generateImage (pixelColor pixels) width height
  savePngImage "mandelbrot.png" (ImageRGBF image)

