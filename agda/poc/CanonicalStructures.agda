module CanonicalStructures where

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

open import Function

record Curry : Set₁ where
  field
    dom : Set
    cur : Set → Set
    prf : (cod : Set) (f : dom → cod) → cur cod
open Curry

curryPair : (A B : Curry) → Curry
curryPair A B =
  record { dom = dom A × dom B
         ; cur = λ cod → cur A (cur B cod)
         ; prf = λ cod f → prf A (cur B cod) $ λ a →
                           prf B cod         $ λ b →
                           f (a , b)
         }

curryDefault : (A : Set) → Curry
curryDefault A =
  record { dom = A
         ; cur = λ cod → A → cod
         ; prf = λ cod → id
         }


postulate
  Target           : (A : Set) → Curry
  Canonical        : (A B : Curry) → Set
  CanonicalProd    : {A B : Set} → Canonical (Target (A × B)) (curryPair (Target A) (Target B))
  CanonicalDefault : {A : Set} →   Canonical (Target A) (curryDefault A)

{-# BUILTIN REWRITE Canonical #-}
{-# REWRITE CanonicalProd     #-}
{-# REWRITE CanonicalDefault  #-}

open import Data.Nat
open import Data.List

infixr 5 flippedMap
flippedMap : {A B : Set} (xs : List (dom (Target A))) (f : cur (Target A) B)  → List B
flippedMap xs f = map f xs

syntax flippedMap xs f = f ⟨$⟩ xs

example : List ℕ
example = _+_ ⟨$⟩ (1 , 2) ∷ (2 , 3) ∷ []
