module Freer.Section2p3

%default total

------------------------------------------------------------------------
-- Type

||| @Free builds many layers of interactions before reaching a value
||| @f    describe the shape each interaction layer has
||| @a    is the type of the returned value
public export
data Free : (Type -> Type) -> (Type -> Type) where
  Pure : a -> Free f a
  Impure : f (Free f a) -> Free f a

------------------------------------------------------------------------
-- Implementations

public export
Functor f => Functor (Free f) where
  map f (Pure a) = Pure (f a)
  map f t@(Impure layer)
    = Impure $ map (\ child => map f (assert_smaller t child)) layer
  -- Unfortunately the indirection introduced by the `f` layer means that
  -- we have to cheat to convince Idris this is terminating.

public export
Functor f => Applicative (Free f) where
  pure = Pure

  Pure f <*> x = map f x
  t@(Impure layer) <*> x
     = Impure $ map (\ child => assert_smaller t child <*> x) layer

public export
Functor f => Monad (Free f) where
  Pure a >>= f = f a
  t@(Impure layer) >>= f
    = Impure (map (\ child => assert_smaller t child >>= f) layer)


------------------------------------------------------------------------
-- Examples

-- Previous examples can now be re-implemented using `Free` by
-- * describing a signature of the effectful interactions available
-- * using a variable to represent the rest of the computation returned by
--   the continuation

namespace Section2p1

  public export
  data ItS : (i, x : Type) -> Type where
    GetS : (i -> x) -> ItS i x

  public export
  It : (i, a : Type) -> Type
  It i = Free (ItS i)

  public export
  Get : (i -> It i a) -> It i a
  Get k = Impure (GetS k)

namespace Section2p2

  public export
  data ItS : (i, o, x : Type) -> Type where
    GetS : () -> (i -> x)  -> ItS i o x
    PutS : o  -> (() -> x) -> ItS i o x

  public export
  It : (i, o, a : Type) -> Type
  It i o = Free (ItS i o)

  public export
  Get : () -> (i -> It i o a)  -> It i o a
  Get v k = Impure (GetS v k)

  public export
  Put : o  -> (() -> It i o a) -> It i o a
  Put v k = Impure (PutS v k)
