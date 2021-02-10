module Freer.Section3p1

import Data.OpenUnion
import Relation.Binary.Closure.Transitive

%default total

------------------------------------------------------------------------
-- Types

mutual

  public export
  Arr : List (Type -> Type) -> Rel Type
  Arr ts a b = a -> Eff ts b

  public export
  Arrs : List (Type -> Type) -> Rel Type
  Arrs ts a b = Closure (Arr ts) a b

  public export
  data Eff : (ts : List (Type -> Type)) -> (Type -> Type) where
    Pure : a -> Eff ts a
    Impure : Union ts v -> Arrs ts v a -> Eff ts a

------------------------------------------------------------------------
-- Implementations

public export
Functor (Eff ts) where
  map f (Pure a) = Pure (f a)
  map f (Impure eff k) = Impure eff (k |> (Pure . f))

public export
Applicative (Eff ts) where
  pure = Pure

  Pure f <*> x = map f x
  Impure eff k <*> x = Impure eff (k |> \ f => map f x)

public export
Monad (Eff ts) where
  Pure a >>= f = f a
  Impure eff k >>= f = Impure eff (k |> f)

------------------------------------------------------------------------
-- Utilities

mutual

  public export
  qApp : Arrs ts a b -> Arr ts a b
  qApp arrs a = case viewL arrs of
    OneL f  => f a
    f <| fs => bind' (f a) (assert_smaller arrs fs)

  public export
  bind' : Eff ts a -> Arrs ts a b -> Eff ts b
  bind' (Pure a) fs = qApp fs a
  bind' (Impure x f) fs = Impure x (add f fs)
