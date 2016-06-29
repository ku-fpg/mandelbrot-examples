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
maxIterations = 1000

-- The number of iterations is the result
mandelbrot :: Prog ()
mandelbrot = do
  (x, y, i) <- structEntity "mandelbrot" $ do
                  x <- newPort "x" In  :: Prog (Signal Int32)
                  y <- newPort "y" In  :: Prog (Signal Int32)
                  i <- newPort "i" Out :: Prog (Signal Int32)
                  return (x, y, i)

  structArchitecture "mandelbrot" "behavioural" $ do
    process [Ident "x", Ident "y", Ident "i"] $ do
      xTemp <- newSignal
      setSignal i 0
      while (do i' <- getSignal i
                x' <- getSignal x
                y' <- getSignal y
                return $ (i' `lt` maxIterations)
                            `and`
                         ((x'*x' + y'*y') `gte` 4))
            (do x' <- getSignal x
                y' <- getSignal y
                setSignal xTemp (x'*x' - x'*y' + x')
                setSignal y (2*x'*y' + y')
                xTemp' <- getSignal xTemp
                setSignal x xTemp'
                i' <- getSignal i
                setSignal i (i' + 1))

-- Print generated VHDL code
main :: IO ()
main = putStrLn $ compile mandelbrot

