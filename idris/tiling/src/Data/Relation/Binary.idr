module Data.Relation.Binary

%default total

public export
REL : Type -> Type -> Type
REL a b = (0 _ : a) -> (0 _ : b) -> Type

public export
Sized : Type
Sized = REL Nat Nat

public export
flip : REL a b -> REL b a
flip r y x = r x y

infixr 1 ~>
public export
(~>) : REL a b -> REL a b -> REL a b
(t ~> u) x y = t x y -> u x y

public export
ary : Nat -> Type -> Type
ary 0 t = t
ary (S n) t = t -> ary n t

public export
lift : (n : Nat) ->
       n `ary` Type ->
       n `ary` REL a b
lift n f = go n (\ _, _ => f) where

  go : (n : Nat) ->
       ((0 _ : a) -> (0 _ : b) -> n `ary` Type) ->
       n `ary` REL a b
  go 0     acc = acc
  go (S n) acc = \ s => go n (\ x, y => acc x y (s x y))

public export
(::) : REL a b -> Type -> Type
t :: _ = {0 x, y : _} -> t x y

public export
Nil : Type
Nil = ()
