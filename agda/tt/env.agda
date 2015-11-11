module tt.env where

open import Data.Nat
open import Data.Fin

open import Function

record Var_=>[_]_ (m : ℕ) (E : ℕ → Set) (n : ℕ) : Set where
  constructor pack
  field lookup : (k : Fin m) → E n
open Var_=>[_]_ public

_⊆_ : (m n : ℕ) → Set
m ⊆ n = Var m =>[ Fin ] n

eps : {n : ℕ} {E : ℕ → Set} → Var 0 =>[ E ] n
lookup eps ()

_∙_ : {n m : ℕ} {E : ℕ → Set} → Var m =>[ E ] n → E n →  Var suc m =>[ E ] n
lookup (ρ ∙ u) = λ k → case k of λ { zero → u; (suc k) → lookup ρ k }

refl : {n : ℕ} → n ⊆ n
lookup refl = id

trans : {m n p : ℕ} → m ⊆ n → n ⊆ p → m ⊆ p
lookup (trans ρmn ρnp) = lookup ρnp ∘ lookup ρmn

step : {m n : ℕ} → m ⊆ n → m ⊆ suc n
lookup (step ρ) = suc ∘ lookup ρ

pop! : {m n : ℕ} → m ⊆ n → suc m ⊆ suc n
pop! ρ = step ρ ∙ zero

extend : {m : ℕ} → m ⊆ suc m
extend = step refl

Weakening : (X : ℕ → Set) → Set
Weakening X = {m n : ℕ} → m ⊆ n → X m → X n

Substituting : (X Y : ℕ → Set) → Set
Substituting X Y = {m n : ℕ} → Y m → Var m =>[ X ] n → Y n

Kripke : (E M : ℕ → Set) (n : ℕ) → Set
Kripke E M n = {m : ℕ} → n ⊆ m → E m → M m

abs : {E M : ℕ → Set} {n : ℕ} → E (suc n) → Kripke E M n → M (suc n)
abs v k = k extend v
