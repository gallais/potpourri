open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; module ≡-Reasoning)

data Ty : Set where
  `nat `bool : Ty

variable
  ty : Ty

⟦_⟧ty : Ty → Set
⟦ `nat  ⟧ty = ℕ
⟦ `bool ⟧ty = Bool

data Expr : Ty → Set where
  `lit : ⟦ ty ⟧ty → Expr ty
  `add : (m n : Expr `nat) → Expr `nat
  `mul : (m n : Expr `nat) → Expr `nat

⟦_⟧ : Expr ty → ⟦ ty ⟧ty
⟦ `lit l   ⟧ = l
⟦ `add m n ⟧ = ⟦ m ⟧ + ⟦ n ⟧
⟦ `mul m n ⟧ = ⟦ m ⟧ * ⟦ n ⟧

Rule : Set
Rule = ∀ ty → Expr ty → Expr ty

simplify : Rule → Rule
simplify f = fgo module Simplify where

  fgo : Rule
  go : Rule

  fgo _ t = f _ (go _ t)

  go _ (`lit l) = `lit l
  go _ (`add m n) = `add (fgo _ m) (fgo _ n)
  go _ (`mul m n) = `mul (fgo _ m) (fgo _ n)

Correct : Rule → Set
Correct r = ∀ ty (e : Expr ty) → ⟦ r ty e ⟧ ≡ ⟦ e ⟧

simplifyᶜ : (r : Rule) → Correct r → Correct (simplify r)
simplifyᶜ r rᶜ = fgoᶜ where

  fgoᶜ : Correct (Simplify.fgo r)
  goᶜ : Correct (Simplify.go r)

  open ≡-Reasoning

  fgoᶜ _ t = begin
    ⟦ Simplify.fgo r _ t ⟧      ≡⟨⟩
    ⟦ r _ (Simplify.go r _ t) ⟧ ≡⟨ rᶜ _ (Simplify.go r _ t) ⟩
    ⟦ Simplify.go r _ t ⟧       ≡⟨ goᶜ _ t ⟩
    ⟦ t ⟧ ∎

  goᶜ _ (`lit t)   = refl
  goᶜ _ (`add m n) = cong₂ _+_ (fgoᶜ _ m) (fgoᶜ _ n)
  goᶜ _ (`mul m n) = cong₂ _*_ (fgoᶜ _ m) (fgoᶜ _ n)

infixr 0 _and_

_and_ : Rule → Rule → Rule
f and g = λ _ t → f _ (g _ t)

0+ : Rule
0+ _ (`add (`lit 0) n) = n
0+ _ t = t

0* : Rule
0* _ (`mul (`lit 0) n) = `lit 0
0* _ t = t

_ : ∀ {a b} → simplify (0* and 0+) _ (`add (`mul (`lit 0) (`lit a)) (`lit b)) ≡ (`lit b)
_ = refl
