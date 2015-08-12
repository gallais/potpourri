module TypeClasses where

open import Data.List as List
open import Data.Product
open import Function

record Curry (A : Set) : Set₁ where
  field
    cur : Set → Set
    prf : (cod : Set) (f : cur cod) → A → cod
open Curry

instance
  curryPair : {A B : Set} {{cA : Curry A}} {{cB : Curry B}} → Curry (A × B)
  curryPair {{cA}} {{cB}} =
    record { cur = λ cod → cur cA (cur cB cod)
           ; prf = λ cod f p → prf cB cod (prf cA (cur cB cod) f (proj₁ p)) (proj₂ p)
           }

curryDefault : (A : Set) → Curry A
curryDefault A =
  record { cur = λ cod → A → cod
         ; prf = λ cod → id
         }

infixr 5 _⟨$⟩_
_⟨$⟩_ : {A : Set} {{cA : Curry A}} {B : Set} (f : cur cA B) (xs : List A) → List B
_⟨$⟩_ {{cA}} f xs = List.map (prf cA _ f) xs

open import Data.Nat

instance
  curryℕ = curryDefault ℕ

example : List ℕ
example = (λ k l m n → k * l + m * n) ⟨$⟩ ((1 , 2) , (3 , 5)) ∷ ((2 , 3) , (4 , 6)) ∷ []