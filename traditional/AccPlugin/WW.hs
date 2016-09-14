{-# LANGUAGE FlexibleContexts #-}

module AccPlugin.WW where

import           Data.Array.Accelerate

abs :: Lift Exp a => a -> Exp (Plain a)
abs = lift

-- | All calls to 'rep' should be gone by the time compilation finishes.
rep :: Exp a -> a
rep = error "Internal error: rep called"

