module tt.env where

open import Data.Nat as ℕ
open import Data.Fin

open import Function

Rel : (E F : ℕ → Set) → Set₁
Rel E F = {n : ℕ} → E n → F n → Set

_⇒_ : (E F : ℕ → Set) → Set
E ⇒ F = {n : ℕ} → E n → F n

record Var_=>[_]_ (m : ℕ) (E : ℕ → Set) (n : ℕ) : Set where
  constructor pack
  field lookup : (k : Fin m) → E n
open Var_=>[_]_ public

∀[_] : {E F : ℕ → Set} (R : Rel E F) {m : ℕ} → Rel (Var m =>[ E ]_) (Var m =>[ F ]_)
∀[ R ] ρ₁ ρ₂ = (k : Fin _) → R (lookup ρ₁ k) (lookup ρ₂ k)

_⊆_ : (m n : ℕ) → Set
m ⊆ n = Var m =>[ Fin ] n

eps : {n : ℕ} {E : ℕ → Set} → Var 0 =>[ E ] n
lookup eps ()

_∙_ : {n m : ℕ} {E : ℕ → Set} → Var m =>[ E ] n → E n →  Var suc m =>[ E ] n
lookup (ρ ∙ u) = λ k → case k of λ { zero → u; (suc k) → lookup ρ k }

refl : {n : ℕ} → n ⊆ n
lookup refl = id

trans : {E : ℕ → Set} {m n p : ℕ} → m ⊆ n → Var n =>[ E ] p → Var m =>[ E ] p
lookup (trans ρmn ρnp) = lookup ρnp ∘ lookup ρmn

step : {m n : ℕ} → m ⊆ n → m ⊆ suc n
lookup (step ρ) = suc ∘ lookup ρ

pop! : {m n : ℕ} → m ⊆ n → suc m ⊆ suc n
pop! ρ = step ρ ∙ zero

extend : {m : ℕ} → m ⊆ suc m
extend = step refl

Weakening : (X : ℕ → Set) → Set
Weakening X = {m n : ℕ} → m ⊆ n → X m → X n

wk[_] : {E : ℕ → Set} {m : ℕ} → Weakening E → Weakening (Var m =>[ E ]_)
lookup (wk[ wk ] inc ρ) k = wk inc (lookup ρ k)

Substituting : (X Y : ℕ → Set) → Set
Substituting X Y = {m n : ℕ} → Y m → Var m =>[ X ] n → Y n

Kripke : (E M : ℕ → Set) (n : ℕ) → Set
Kripke E M n = {m : ℕ} → n ⊆ m → E m → M m

abs : {E M : ℕ → Set} {n : ℕ} → E (suc n) → Kripke E M n → M (suc n)
abs v k = k extend v

