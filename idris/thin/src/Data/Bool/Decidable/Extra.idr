||| This should probably go into Idris 2's standard library

module Data.Bool.Decidable.Extra

import Data.Bool.Decidable

-- The Reflects family is defined in Idris 2's standard library's module
-- Data.Bool.Decidable. It is defined like so:
--   data Reflects : Type -> Bool -> Type where
--     RTrue : p -> Reflects p True
--     RFalse : Not p -> Reflects p False

-- A proof of (Reflects p b) states that the boolean value b reflects
-- whether p holds or not.

import Data.Nat
import Decidable.Equality

%default total

------------------------------------------------------------------------
-- Properties of Reflects
------------------------------------------------------------------------

||| If p & q are equivalent types then if b reflects p, it also reflects q
export
mapReflects : p <=> q -> Reflects p b -> Reflects q b
mapReflects pq (RTrue p) = RTrue (leftToRight pq p)
mapReflects pq (RFalse np) = RFalse (np . rightToLeft pq)

||| Equivalence is symmetric
export
symmetric : p <=> q -> q <=> p
symmetric (MkEquivalence f g) = MkEquivalence g f

||| If p & q are equivalent then so are (Reflects p b) & (Reflects q b)
export
reflectsEquiv : p <=> q -> Reflects p b <=> Reflects q b
reflectsEquiv pq = MkEquivalence (mapReflects pq) (mapReflects $ symmetric pq)

||| Product types are adequately reflected by the boolean conjunction
||| of each component's respective reflection
export
andReflects : Reflects p b -> Reflects q c -> Reflects (p, q) (b && c)
andReflects (RTrue p) (RTrue q) = RTrue (p, q)
andReflects (RTrue p) (RFalse nq) = RFalse (nq . snd)
andReflects (RFalse np) rq = RFalse (np . fst)

||| Sums types are adequately reflected by the boolean disjunction
||| of each component's respective reflection
export
orReflects : Reflects p b -> Reflects q c -> Reflects (Either p q) (b || c)
orReflects (RTrue p) _ = RTrue (Left p)
orReflects (RFalse np) (RTrue q) = RTrue (Right q)
orReflects (RFalse np) (RFalse nq) = RFalse (either np nq)

||| Boolean equality on natural numbers as defined in the standard library
||| adequately reflects propositional equality. Proven by induction.
export
reflectsNat : (m, n : Nat) -> Reflects (m === n) (m == n)
reflectsNat 0 0 = RTrue Refl
reflectsNat 0 (S _) = RFalse absurd
reflectsNat (S _) 0 = RFalse absurd
reflectsNat (S m) (S n)
  = mapReflects (MkEquivalence (cong S) injective)
  $ reflectsNat m n

||| Boolean equality of integers as defined in the standard library reflects
||| their propositional equality.
||| We can prove this thanks to the fact that DecEq for Integers is implemented
||| using boolean equality
export
reflectsInteger : (bs, cs : Integer) -> Reflects (bs === cs) (bs == cs)
reflectsInteger bs cs with (decEq bs cs) proof eq
  _ | p with (bs == cs)
    reflectsInteger bs cs | Yes prf | True = RTrue prf
    reflectsInteger bs cs | No nprf | False = RFalse nprf


||| If we know there's a boolean that reflects a type then the type is decidable
export
toDec : Reflects p b -> Dec p
toDec (RTrue yes) = Yes yes
toDec (RFalse no) = No no
