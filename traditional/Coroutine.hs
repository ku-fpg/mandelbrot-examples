{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Coroutine where

import           Control.Monad (liftM, ap)

data CoroutineT a m b r where
  Lift   :: m r -> CoroutineT a m b r
  Bind   :: CoroutineT a m b x -> (x -> CoroutineT a m b r) -> CoroutineT a m b r
  Await  :: a -> CoroutineT a m b b

instance Applicative m => Functor (CoroutineT a m b) where fmap = liftM
instance Applicative m => Applicative (CoroutineT a m b) where
  pure = return
  (<*>) = ap

instance Applicative m => Monad (CoroutineT a m b) where
  return = Lift . pure
  (>>=)  = Bind

withProducer :: Monad m => (a -> m b) -> CoroutineT a m b r -> m r
withProducer _        (Lift mr)    = mr
withProducer producer (Bind mx mf) = withProducer producer mx >>= (withProducer producer . mf)
withProducer producer (Await arg)  = producer arg

