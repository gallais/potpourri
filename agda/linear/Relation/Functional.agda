module linear.Relation.Functional where

open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality

Functional :
  {RI : Set}      -- Relevant Input
  {II : RI → Set} -- Irelevant Input
  {O  : RI → Set} -- Output
  (R  : (ri : RI) → II ri → O ri → Set) → Set
Functional {RI} {II} {O} R =
  (ri : RI) {ii₁ ii₂ : II ri} {o₁ o₂ : O ri} →
  R ri ii₁ o₁ → R ri ii₂ o₂ → o₁ ≡ o₂

Functional′ : {I : Set} {O : I → Set} (R : (i : I) → O i → Set) → Set
Functional′ R = Functional {II = const ⊤} (λ ri _ o → R ri o)
