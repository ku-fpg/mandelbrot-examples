{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module AccPlugin.WW where

import           Data.Array.Accelerate

abs :: (Lift Exp a, a ~ Plain a) => a -> Exp a
abs = lift

-- | All calls to 'rep' should be gone by the time compilation finishes.
rep :: Exp a -> a
rep = error "Internal error: rep called"

plainRep :: a -> Plain a
plainRep = error "Internal error: plainRep called"

