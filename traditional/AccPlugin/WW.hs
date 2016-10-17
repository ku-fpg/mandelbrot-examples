{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module AccPlugin.WW where

import           Data.Array.Accelerate

abs :: (Lift Exp a, a ~ Plain a) => a -> Exp a
abs = lift
{-# NOINLINE abs #-}

-- | All calls to 'rep' should be gone by the time compilation finishes.
rep :: Exp a -> a
rep _ = error "Internal error: rep called"
{-# NOINLINE rep #-}

-- plainRep :: a -> Plain a
-- plainRep _ = error "Internal error: plainRep called"
-- {-# NOINLINE plainRep #-}

