module ConstN

import Data.Vect
import Data.Fun
import Data.Vect.Quantifiers

%default total

namespace Fun

  public export
  uncurry : (ts : Vect n Type) -> Fun ts a -> All Prelude.id ts -> a
  uncurry [] f vs = f
  uncurry (t :: ts) f (v :: vs) = uncurry ts (f v) vs

  public export
  curry : (ts : Vect n Type) -> (All Prelude.id ts -> a) -> Fun ts a
  curry [] f = f []
  curry (t :: ts) f = \ v => curry ts (f . (v ::))

Forall : {t : Type} -> (n : Nat) -> (Vect n t -> Type) -> Type
Forall 0 p = p []
Forall (S k) p = {x : t} -> Forall k (p . (x ::))

namespace Forall

  public export
  uncurry : (n : Nat) -> {0 p : Vect n t -> Type} ->
            Forall n p -> ((ts : Vect n t) -> p ts)
  uncurry Z f [] = f
  uncurry (S n) f (v :: vs) = uncurry n {p = p . (v ::)} f vs

  public export
  curry : (n : Nat) -> {0 p : Vect n t -> Type} ->
          ((ts : Vect n t) -> p ts) -> Forall n p
  curry Z f = f []
  curry (S n) f = curry n {p = p . (_ ::)} (\ vs => f (_ :: vs))

ConstN : (n : Nat) -> Type -> Type
ConstN n a = Forall n (\ ts => Fun ts a)

constN : (n : Nat) -> a -> ConstN n a
constN n v = Forall.curry n
           $ \ _ => Fun.curry _
           $ \ _ => v

Eq () where
  (==) = constN 2 True

test : ?
test = constN 3 "test" 1 2 3
