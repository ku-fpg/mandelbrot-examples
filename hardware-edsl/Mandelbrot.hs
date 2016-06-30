{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

import           Prelude hiding (and)

import           Language.VHDL hiding (Ident)
import           Language.Embedded.Hardware

import           Control.Monad.Identity
import           Control.Monad.Operational.Higher
import           Data.ALaCarte
import           Data.Int

type CMD =
      SignalCMD       HExp
  :+: VariableCMD     HExp
  :+: ArrayCMD        HExp
  :+: VArrayCMD       HExp
  :+: LoopCMD         HExp
  :+: ConditionalCMD  HExp
  :+: ComponentCMD    HExp
  :+: StructuralCMD   HExp

type Prog = Program CMD

maxIterations :: HExp Int32
maxIterations = 100

-- The number of iterations is the result
mandelbrot :: Prog ()
mandelbrot = do
  (x, y, i) <- structEntity "mandelbrot" $ do
                  x <- newPort "x" In  :: Prog (Signal Int32)
                  y <- newPort "y" In  :: Prog (Signal Int32)
                  i <- newPort "i" Out :: Prog (Signal Int32)
                  return (x, y, i)

  structArchitecture "mandelbrot" "behavioural" $ do
    process (x .: y .: []) $ do
      xTemp <- initNamedVariable "xTemp" 0

      xInit <- getSignal x
      yInit <- getSignal y

      xv <- initNamedVariable "xv" xInit
      yv <- initNamedVariable "yv" yInit
      iv <- initNamedVariable "iv" 0

      while (do i' <- getVariable iv
                x' <- getVariable xv
                y' <- getVariable yv
                return $ (i' `lt` maxIterations)
                            `and`
                         ((x'*x' + y'*y') `gte` 4))

            (do x' <- getSignal x
                y' <- getSignal y
                setVariable xTemp (x'*x' - x'*y' + x')
                xTemp' <- getVariable xTemp
                setVariable yv (2*xTemp'*y' + y')
                setVariable xv xTemp'
                i' <- getVariable iv
                setVariable iv (i' + 1))

      i' <- getVariable iv
      setSignal i i'

-- Print generated VHDL code
main :: IO ()
main = putStrLn $ compile mandelbrot
-- main = runIO mandelbrot

