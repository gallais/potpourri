{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Conc5 where

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

type MAction m a = Either a (Action m a)

data Action m a where
  Pure :: a -> Action m a
  Atom :: m (Action m a) -> Action m a
  Join :: Action m b
       -> Action m c
       -> (b -> c -> MAction m a)
       -> Action m a

type Conc m a = forall r. Cont (Action m r) a

action :: Conc m a -> Action m a
action (MkCont c) = c Pure

atom :: Functor m => m a -> Conc m a
atom m = MkCont $ \ k -> Atom (k <$> m)

fork :: Conc m () -> Conc m ()
fork c = MkCont $ \ k ->
  Join (action c) (k ()) $ \ a b -> Left b

conc :: Conc m a -> Conc m b -> Conc m (a, b)
conc c1 c2 = MkCont $ \ k ->
  Join (action c1) (action c2) $ \ a b ->
  Right $ k (a, b)

await :: Conc m a -> Conc m a
await c = MkCont $ \ k -> Join (action c) (Pure ()) (const . Right . k)

data TreeAct m a where
  ALeaf   :: Action m a -> TreeAct m a
  ABranch :: (a -> MAction m b)
          -> TreeAct m a
          -> TreeAct m b
  ANode   :: (a -> b -> Either c (Action m c))
          -> TreeAct m a
          -> TreeAct m b
          -> TreeAct m c

data Stack m :: Type -> Type -> Type where
  SNil   :: Stack m a a
  SCons  :: (a -> MAction m c)
         -> Stack m c ret
         -> Stack m a ret
  SConsL :: (a -> b -> MAction m c)
         -> Stack m c ret
         -> TreeAct m b
         -> Stack m a ret
  SConsR :: (a -> b -> MAction m c)
         -> TreeAct m a
         -> Stack m c ret
         -> Stack m b ret

unwind
  :: Monad m
  => a
  -> Stack m a ret
  -> m ret
unwind v SNil = pure v
unwind v (SCons f stk) = case f v of
  Left fv -> unwind fv stk
  Right fv -> next (ALeaf fv) stk
unwind v (SConsL f stk t) = robin t (SCons (f v) stk)
unwind v (SConsR f t stk) = next (ABranch (flip f v) t) stk

next
  :: Monad m
  => TreeAct m a
  -> Stack m a ret
  -> m ret
next t SNil = robin t SNil
next t (SCons f stk) = next (ABranch f t) stk
next t (SConsL f stk t') = robin t' (SConsR f t stk)
next t (SConsR f t' stk) = next (ANode f t' t) stk

robin
  :: Monad m
  => TreeAct m a
  -> Stack m a ret
  -> m ret
robin (ALeaf a) stk = case a of
  Pure v -> unwind v stk
  Atom c -> do
    a <- c
    next (ALeaf a) stk
  Join a1 a2 j -> next (ANode j (ALeaf a1) (ALeaf a2)) stk
robin (ABranch f a) stk = robin a (SCons f stk)
robin (ANode f a1 a2) stk = robin a1 (SConsL f stk a2)


run :: Monad m => Conc m a -> m a
run c = robin (ALeaf (action c)) SNil

loop :: Int -> String -> Conc IO Int
loop i s
  | i <= 0 = pure (length s)
  | otherwise = do atom (putStrLn s); loop (i - 1) s

example :: Conc IO Int
example = do
  atom $ putStrLn "start!"
  fork (void $ loop 5 "fish")
  i <- do fork (void $ loop 5 "cat"); loop 5 "catfish"
  j <- loop 5 "finalising"
  atom $ putStrLn "end!"
  atom $ pure (i + j)

fibonacci :: Int -> Int -> Conc IO Int
fibonacci i n | n <= 1 = do
  atom $ putStrLn $ unwords
    [ "Thread", show i, "has reached the base case: fib", show n, "=", show n ]
  pure n
fibonacci i n = do
  let i1 = (2*i)
  let i2 = i1+1
  atom $ putStrLn $ unwords
    [ "Thread", show i, "is spawning threads"
    , show i1, "and", show i2
    , "concurrently"]
  (fn1, fn2) <- conc (fibonacci i1 (n-1)) (fibonacci i2 (n-2))
  await (loop 3 $ unwords [ "Thread", show i, "waiting" ])
  let fn = fn1 + fn2
  atom $ putStrLn $ unwords
    [ "Thread", show i, "has computed fib", show n, "=", show fn ]
  pure fn
