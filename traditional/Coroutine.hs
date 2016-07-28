{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Coroutine where

import           Control.Remote.Monad

data Cmd :: (* -> *) -> * -> * where
  Continue :: m r -> Cmd m r

data Proc :: * -> * -> * where
  Await :: a -> Proc b b

type CoroutineT a m b r = RemoteMonad (Cmd m r) (Proc b) r

await :: a -> CoroutineT a m b b
await = procedure . Await

withProducer :: Monad m => (a -> m b) -> CoroutineT a m b r -> m r
withProducer = undefined

