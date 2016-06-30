{-# LANGUAGE Strict #-}

import           Codec.Picture

maxIterations :: Int
maxIterations = 100

width, height :: Int
width  = 800
height = 600

-- Scale x to [-2.5, 1] and y to [-1, 1]
scaleX, scaleY :: Float -> Float
scaleX x = -2.5 + x * ((2.5 + 1) / fromIntegral width)
scaleY y = -1 + y * ((1 + 1) / fromIntegral height)

pointColor :: Int -> Int -> PixelRGBF
pointColor origX' origY' = go 0 0 0
  where
    origX = fromIntegral origX'
    origY = fromIntegral origY'

    (scaledX, scaledY) = (scaleX origX, scaleY origY)

    go n x y
      | n >= maxIterations = PixelRGBF 0 0 1
      | x^2 + y^2 >= 4     = PixelRGBF (fromIntegral n/fromIntegral maxIterations) 0 0
      | otherwise          = go (n+1)
                                (x^2 - y^2 + scaledX)
                                (2*x*y + scaledY)

main :: IO ()
main = do
  let image = generateImage pointColor width height
  savePngImage "mandelbrot.png" (ImageRGBF image)

