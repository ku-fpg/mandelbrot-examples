{-# LANGUAGE FlexibleContexts #-}

module AccPlugin.WW where

import           Data.Array.Accelerate

rep :: Lift Exp a => a -> Exp (Plain a)
rep = lift

-- | All calls to 'abs' should be gone by the time compilation finishes.
abs :: Exp a -> a
abs = error "Internal error: abs called"

