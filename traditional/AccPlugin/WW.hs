{-# LANGUAGE FlexibleContexts #-}

module AccPlugin.WW where

import           Data.Array.Accelerate

-- abs :: Lift Exp a => a -> Exp (Plain a)
abs :: Lift Exp a => a -> Exp a
abs = prf . lift
  where
    prf :: (Lift Exp x) => Exp (Plain x) -> Exp x
    prf = undefined

-- | All calls to 'rep' should be gone by the time compilation finishes.
rep :: Exp a -> a
rep = error "Internal error: rep called"

