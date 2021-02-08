module Freer.Section2p5

import Union

%default total

------------------------------------------------------------------------
-- Type

public export
data FEFree : (ts : List (Type -> Type)) -> Type -> Type where
  Pure : a -> FEFree ts a
  Impure : Union ts x -> (x -> FEFree ts a) -> FEFree ts a

------------------------------------------------------------------------
-- Examples

public export
data Reader : (i, x : Type) -> Type where
  Get : Reader i i

public export
data Writer : (o, x : Type) -> Type where
  Put : o -> Writer o ()

------------------------------------------------------------------------
-- Implementation

Functor (FEFree ts) where
  map f (Pure a) = Pure (f a)
  map f (Impure eff k) = Impure eff (\ i => map f (k i))

public export
Applicative (FEFree ts) where
  pure = Pure

  Pure f <*> x = map f x
  Impure eff k <*> x = Impure eff (\ i => k i <*> x)

public export
Monad (FEFree ts) where
  Pure a >>= f = f a
  Impure eff k >>= f = Impure eff (\ i => k i >>= f)

------------------------------------------------------------------------
-- Examples

public export
ask : Member (Reader i) ts => FEFree ts i
ask = Impure (inj Get) Pure
