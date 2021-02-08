module Freer.Section2p1

import Data.List
import Data.Stream

%default total

------------------------------------------------------------------------
-- Type

||| @It describes an interaction corresponding to a Reader effect.
||| i  is the type of inputs one may request
||| a  is the type of the computation's output
public export
data It : (i, a : Type) -> Type where
-- Effect-free computation: return a value
  Pure : a -> It i a
-- Effectful computation
--      Continuation
  Get : (i -> It i a) -> It i a

------------------------------------------------------------------------
-- Example

||| @ask is the interaction requesting an input & just returning it
public export
ask : It i i
ask = Get Pure

------------------------------------------------------------------------
-- Composing interactions is done using the Monad implementation

public export
Functor (It i) where
  map f (Pure a) = Pure (f a)
  map f (Get k)  = Get (\ i => map f (k i))

public export
Applicative (It i) where
  pure = Pure
  Pure f <*> x = map f x
  Get k  <*> x = Get (\ i => k i <*> x)

public export
Monad (It i) where
  Pure x >>= f = f x
  Get k  >>= f = Get (\ i => k i >>= f)

------------------------------------------------------------------------
-- Examples

public export
addGet : Int -> It Int Int
addGet inc = do i <- ask
                pure (i + inc)

public export
addN : Nat -> It Int Int
addN n = foldl (>>>) pure (replicate n addGet) 0

------------------------------------------------------------------------
-- Execution

||| Using a given input i, run the interaction answering all of the Get
||| questions by returning i.
public export
runReader : i -> It i a -> a
runReader i (Pure a) = a
runReader i (Get k) = runReader i (k i)

||| Using a stream of inputs, run the interaction answering the successive
||| Get calls with successive values taken from the stream.
public export
feedAll : Stream i -> It i a -> a
feedAll is (Pure a) = a
feedAll (i :: is) (Get k) = feedAll is (k i)
