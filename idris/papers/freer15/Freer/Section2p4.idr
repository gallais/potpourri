module Freer.Section2p4

%default total

------------------------------------------------------------------------
-- Type

||| @FFree is just like Free defined in Freer.Section2p3 except that the
||| layers are presented side-by-side instead of nested as a tree.
|||
||| It's the same as seeing the natural number 3 as:
||| `S S S Z`      (nested subterms, Free-style)
||| `[(), (), ()]` (sequence of layers, FFree style)
|||
||| Note that `Impure` implicitly quantifies over `x`, the return type of
||| the effectful interaction. This should typically make `FFree f a` one
||| level larger than its argument `f`. However Idris currently does not
||| have a universe checker so we can do whatever we want here.
public export
data FFree : (Type -> Type) -> (Type -> Type) where
  Pure : a -> FFree f a
  Impure : f x -> (x -> FFree f a) -> FFree f a

------------------------------------------------------------------------
-- Examples

namespace Section2p1

  ||| @ItS describes one layer of interaction with Reader actions available
  ||| @i   is the type of inputs one may request
  ||| @x   is the return type of the interaction
  public export
  data ItS : (i, x : Type) -> Type where
    Get : ItS i i

  public export
  It : (i, a : Type) -> Type
  It i = FFree (ItS i)

namespace Section2p2

  ||| @ItS describes one layer of interaction with both Reader and Writer
  |||      effectful actions available.
  ||| @i   is the type of inputs one may request
  ||| @o   is the type of outputs one may emit
  ||| @x   is the return type of the interaction. It corresponds to the domain
  |||      of the respective continuations used in previous sections.
  public export
  data ItS : (i, o, x : Type) -> Type where
    Get : () -> ItS i o i
    Put : o  -> ItS i o ()

  public export
  It : (i, o, a : Type) -> Type
  It i o = FFree (ItS i o)

------------------------------------------------------------------------
-- Implementation

-- Note that now that the indirection introduced by the (uninspectable) layer
-- of `f` has been removed in favour of explicit "sequencing", we no longer
-- have to cheat to convince Idris that these functions are terminating

public export
Functor (FFree f) where
  map f (Pure a) = Pure (f a)
  map f (Impure eff k) = Impure eff (\ i => map f (k i))

public export
Applicative (FFree f) where
  pure = Pure

  Pure f <*> x = map f x
  Impure eff k <*> x = Impure eff (\ i => k i <*> x)

public export
Monad (FFree f) where
  Pure a >>= f = f a
  Impure eff k >>= f = Impure eff (\ i => k i >>= f)

------------------------------------------------------------------------
-- Left-Kan extension detour

public export
data Lan : (Type -> Type) -> (Type -> Type) where
  Map : (x -> a) -> f x -> Lan f a

public export
Functor (Lan f) where
  map f (Map g t) = Map (f . g) t
