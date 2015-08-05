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
    prf : (cod : Set) (f : cur cod) → dom → cod
open Curry

curryPair : (A B : Curry) → Curry
curryPair A B =
  record { dom = dom A × dom B
         ; cur = λ cod → cur A (cur B cod)
         ; prf = λ cod f p → prf B cod (prf A (cur B cod) f (fst p)) (snd p)
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

infixr 5 flippedMap'
flippedMap : {A : Curry} {B : Set} (xs : List (dom A)) (f : cur A B)  → List B
flippedMap {A} xs f = map (prf A _ f) xs

flippedMap' : {A B : Set} (xs : List (dom (Target A))) (f : cur (Target A) B)  → List B
flippedMap' {A} = flippedMap {Target A}

syntax flippedMap' xs f = f ⟨$⟩ xs

example : List ℕ
example = (λ k l m n → k * l + m * n) ⟨$⟩ ((1 , 2) , (3 , 5)) ∷ ((2 , 3) , (4 , 6)) ∷ []
