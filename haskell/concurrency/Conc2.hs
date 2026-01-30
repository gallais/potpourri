{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Conc2 where

import Data.Functor (void)
import Data.Kind (Type)

------------------------------------------------------------------------
-- Continuation monad

newtype Cont r a = MkCont { runCont :: (a -> r) -> r }

instance Functor (Cont r) where
  fmap f (MkCont c) = MkCont (c . (. f))

instance Applicative (Cont r) where
  pure a = MkCont ($ a)
  MkCont mf <*> MkCont ma = MkCont $ \ k ->
    mf $ \ f ->
    ma $ \ a ->
    k (f a)

instance Monad (Cont r) where
  MkCont ma >>= f = MkCont $ \ k ->
    ma $ \ a ->
    runCont (f a) k

execCont :: Cont a a -> a
execCont (MkCont c) = c id

------------------------------------------------------------------------
-- Concurrency monad

data Action m a where
  Pure :: a -> Action m a
  Atom :: m (Action m a) -> Action m a
  Fork :: Action m () -- Fork is right-biased
       -> Action m a
       -> Action m a

type Conc m r a = Cont (Action m r) a

action :: Conc m a a -> Action m a
action (MkCont c) = c Pure

atom :: Functor m => m a -> Conc m r a
atom m = MkCont $ \ k -> Atom (k <$> m)

fork :: Conc m () () -> Conc m a ()
fork c = MkCont (\ k -> Fork (action c) (k ()))

data All (p :: Type -> Type) (as :: [Type]) where
  ANil  :: All p '[]
  ACons :: p a -> All p as -> All p (a : as)

newtype Identity a = MkIdentity { runIdentity :: a }

instance Functor Identity where
  fmap f = MkIdentity . f . runIdentity

instance Applicative Identity where
  pure = MkIdentity
  f <*> x = MkIdentity (runIdentity f $ runIdentity x)

instance Monad Identity where
  x >>= f = f $ runIdentity x


rewind :: Monad m
       => (All Identity sa -> All Identity as -> b)
       -> All (Action m) sa
       -> All (Action m) as
       -> m b
rewind f (ACons a sa) as = rewind (\ sv (ACons v vs) -> f (ACons v sv) vs) sa (ACons a as)
rewind f sa as = robin f sa as

robin :: Monad m
      => (All Identity sa -> All Identity as -> b)
      -> All (Action m) sa
      -> All (Action m) as
      -> m b
robin f ANil ANil = pure (f ANil ANil)
robin f sa (ACons a as) = case a of
    Atom c -> do
      a <- c
      robin (\ (ACons v sv) vs -> f sv (ACons v vs)) (ACons a sa) as
    Fork a1 a2 -> robin (\ (ACons v (ACons _ sv)) vs -> f sv (ACons v vs)) (ACons a2 (ACons a1 sa)) as
    Pure v -> robin (\ sv vs -> f sv (ACons (MkIdentity v) vs)) sa as
robin f sa as = rewind f sa as


run :: Monad m => Conc m a a -> m a
run c = robin (\ _ (ACons v _) -> runIdentity v) ANil (ACons (action c) ANil)

loop :: Int -> String -> Conc IO a Int
loop i s
  | i <= 0 = pure (length s)
  | otherwise = do atom (putStrLn s); loop (i - 1) s


example :: Conc IO Int Int
example = do
  atom $ putStrLn "start!"
  fork (void $ loop 5 "fish")
  i <- do fork (void $ loop 5 "cat"); loop 5 "catfish"
  j <- loop 5 "finalising"
  atom $ putStrLn "end!"
  atom $ pure (i + j)
