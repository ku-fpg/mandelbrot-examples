{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Coroutine where

import           Control.Monad (liftM, ap)

import           Control.Monad.Trans

data CoroutineT a m b r where
  Lift   :: m r -> CoroutineT a b m r
  Bind   :: CoroutineT a b m x -> (x -> CoroutineT a b m r) -> CoroutineT a b m r
  Await  :: a -> CoroutineT a b m b

instance Applicative m => Functor (CoroutineT a b m) where fmap = liftM
instance Applicative m => Applicative (CoroutineT a b m) where
  pure = return
  (<*>) = ap

instance Applicative m => Monad (CoroutineT a b m) where
  return = Lift . pure
  (>>=)  = Bind

instance MonadTrans (CoroutineT a b) where
  lift = Lift

withProducer :: Monad m => (a -> m b) -> CoroutineT a b m r -> m r
withProducer _        (Lift mr)    = mr
withProducer producer (Bind mx mf) = withProducer producer mx >>= (withProducer producer . mf)
withProducer producer (Await arg)  = producer arg

