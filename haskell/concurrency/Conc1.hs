-- The content of this module is based on
-- A poor man's concurrency monad
-- by Koen Claessen

module Conc1 where

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

data Action m
  = Atom (m (Action m))
  | Fork (Action m) (Action m)
  | Stop

type Conc m = Cont (Action m)

action :: Conc m a -> Action m
action (MkCont c) = c $ const Stop

atom :: Functor m => m a -> Conc m a
atom m = MkCont $ \ k -> Atom (k <$> m)

stop :: Conc m a
stop = MkCont $ const Stop

fork :: Conc m a -> Conc m ()
fork c = MkCont $ \ k ->
  Fork (action c) (k ())

data Queue a = MkQueue
  { fwd :: [a]
  , bwd :: [a]
  }

empty :: Queue a
empty = MkQueue [] []

enqueue :: Queue a -> a -> Queue a
enqueue (MkQueue fwd bwd) x = MkQueue fwd (x : bwd)

dequeue :: Queue a -> Maybe (a, Queue a)
dequeue (MkQueue [] []) = Nothing
dequeue (MkQueue (x : fwd) bwd) = Just (x, MkQueue fwd bwd)
dequeue (MkQueue [] bwd) = dequeue (MkQueue (reverse bwd) [])

robin :: Monad m => Queue (Action m) -> m ()
robin q = case dequeue q of
  Nothing -> pure ()
  Just (a, q) -> case a of
    Atom c -> do
      c' <- c
      robin (enqueue q c')
    Fork a1 a2 -> robin ((q `enqueue` a1) `enqueue` a2)
    Stop -> robin q

run :: Monad m => Conc m a -> m ()
run c = robin (enqueue empty (action c))

loop :: Int -> String -> Conc IO ()
loop i s
  | i <= 0 = pure ()
  | otherwise = do atom (putStrLn s); loop (i - 1) s


example :: Conc IO ()
example = do
  atom $ putStrLn "start!"
  fork (loop 5 "fish")
  loop 5 "cat"
  atom $ putStrLn "end!"
