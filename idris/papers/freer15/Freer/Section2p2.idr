module Freer.Section2p2

import Data.List
import Data.Stream

%default total

------------------------------------------------------------------------
-- Type

||| @It describes an interaction corresponding to the combination of a
||| Reader and Writer effects.
||| i  is the type of inputs one may request
||| o  is the type of inputs one may write
||| a  is the type of the computation's output
public export
data It : (i, o, a : Type) -> Type where
  Pure : a -> It i o a
-- Effectful interactions: provided an argument, the machine will perform
-- some operation and call yourself back with a result using the continuation.
-- For uniformity, we add an extra argument to `Get`: (), the dummy argument.
  Get  : () -> (i -> It i o a)  -> It i o a
  Put  : o  -> (() -> It i o a) -> It i o a

------------------------------------------------------------------------
-- Example

||| @ask is the interaction requesting an input & just returning it
public export
ask : It i o i
ask = Get () Pure

||| @tell is the interaction writing a value & returning nothing
public export
tell : o -> It i o ()
tell o = Put o Pure

------------------------------------------------------------------------
-- Composing interactions is done using the Monad implementation

public export
Functor (It i o) where
  map f (Pure a) = Pure (f a)
  map f (Get () k) = Get () (\ i => map f (k i))
  map f (Put o k) = Put o (\ i => map f (k i))

public export
Applicative (It i o) where
  pure = Pure
  Pure f <*> x = map f x
  Get () k  <*> x = Get () (\ i => k i <*> x)
  Put o k <*> x = Put o (\ i => k i <*> x)

public export
Monad (It i o) where
  Pure x >>= f = f x
  Get () k  >>= f = Get () (\ i => k i >>= f)
  Put o k >>= f = Put o (\ i => k i >>= f)

------------------------------------------------------------------------
-- Examples: same code, different types

public export
addGet : Int -> It Int o Int
addGet inc = do i <- ask
                pure (i + inc)

public export
addN : Nat -> It Int o Int
addN n = foldl (>>>) pure (replicate n addGet) 0

------------------------------------------------------------------------
-- Execution

||| Using a given input i, run the interaction answering all of the Get
||| questions by returning i. Combine the written values in the output
||| value of type o using the monoid.
public export
runRdWriter : Monoid o => i -> It i o a -> (a, o)
runRdWriter v = loop neutral where

  loop : o -> It i o a -> (a, o)
  loop acc (Pure a) = (a, acc)
  loop acc (Get () k) = loop acc (k v)
  loop acc (Put o k) = loop (acc <+> o) (k ())

||| Only keeping the last output value
public export
keepLast : i -> It i o a -> (a, Maybe o)
keepLast v = loop Nothing where

  loop : Maybe o -> It i o a -> (a, Maybe o)
  loop acc (Pure a) = (a, acc)
  loop acc (Get () k) = loop acc (k v)
  loop _ (Put o k) = loop (Just o) (k ())

||| When the input and output types are the same, we can use the outputs
||| as updates to replace the input with.
public export
asState : s -> It s s a -> (a, s)
asState s (Pure a) = (a, s)
asState s (Get () k) = asState s (k s)
asState _ (Put s k) = asState s (k ())
