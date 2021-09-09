module Data.Either.Relation

import Control.Relation

import Data.Either
import Data.Relation

public export
data Pointwise : Rel x -> Rel y -> Rel (Either x y) where
  PLeft  : {0 p : Rel x} -> p x1 x2 -> Pointwise p q (Left x1)  (Left x2)
  PRight : {0 q : Rel y} -> q y1 y2 -> Pointwise p q (Right y1) (Right y2)

export
pointwiseBimap : (p ~> p') -> (q ~> q') -> (Pointwise p q ~> Pointwise p' q')
pointwiseBimap f g (PLeft x)  = PLeft (f x)
pointwiseBimap f g (PRight x) = PRight (g x)

export
mirror : Pointwise p q x y -> Pointwise q p (mirror x) (mirror y)
mirror (PLeft prf)  = PRight prf
mirror (PRight prf) = PLeft prf

export
comirror : {x, y : Either a b} ->
           Pointwise q p (mirror x) (mirror y) -> Pointwise p q x y
comirror {x = Left _}  {y = Left _}  (PRight prf) = PLeft prf
comirror {x = Right _} {y = Right _} (PLeft prf)  = PRight prf

export
and : Pointwise p q x y -> Pointwise r s x y ->
      Pointwise (And p r) (And q s) x y
and (PLeft p)  (PLeft r)  = PLeft (p, r)
and (PRight q) (PRight s) = PRight (q, s)
