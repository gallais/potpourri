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

record Correct (r : Rule) : Set where
  field runCorrect : ∀ {ty} (e : Expr ty) → ⟦ r ty e ⟧ ≡ ⟦ e ⟧
open Correct

simplifyᶜ : (r : Rule) → Correct r → Correct (simplify r)
simplifyᶜ r rᶜ = fgoᶜ where

  fgoᶜ : Correct (Simplify.fgo r)
  goᶜ : Correct (Simplify.go r)

  open ≡-Reasoning

  fgoᶜ .runCorrect t = begin
    ⟦ Simplify.fgo r _ t ⟧      ≡⟨⟩
    ⟦ r _ (Simplify.go r _ t) ⟧ ≡⟨ rᶜ .runCorrect (Simplify.go r _ t) ⟩
    ⟦ Simplify.go r _ t ⟧       ≡⟨ goᶜ .runCorrect t ⟩
    ⟦ t ⟧ ∎

  goᶜ .runCorrect (`lit t)   = refl
  goᶜ .runCorrect (`add m n) = cong₂ _+_ (fgoᶜ .runCorrect m) (fgoᶜ .runCorrect n)
  goᶜ .runCorrect (`mul m n) = cong₂ _*_ (fgoᶜ .runCorrect m) (fgoᶜ .runCorrect n)

infixr 0 _and_

_and_ : Rule → Rule → Rule
f and g = λ _ t → f _ (g _ t)

0+ : Rule
0+ _ (`add (`lit 0) n) = n
0+ _ t = t


0+ᶜ : Correct 0+
0+ᶜ .runCorrect (`lit l) = refl
0+ᶜ .runCorrect (`add (`lit zero) n) = refl
0+ᶜ .runCorrect (`add (`lit (suc l)) n) = refl
0+ᶜ .runCorrect (`add (`add m n) p) = refl
0+ᶜ .runCorrect (`add (`mul m n) p) = refl
0+ᶜ .runCorrect (`mul m n) = refl

0* : Rule
0* _ (`mul (`lit 0) n) = `lit 0
0* _ t = t

0*ᶜ : Correct 0*
0*ᶜ .runCorrect (`lit l) = refl
0*ᶜ .runCorrect (`add m n) = refl
0*ᶜ .runCorrect (`mul (`lit 0) n) = refl
0*ᶜ .runCorrect (`mul (`lit (suc _)) n) = refl
0*ᶜ .runCorrect (`mul (`add m n) p) = refl
0*ᶜ .runCorrect (`mul (`mul m n) p) = refl

_andᶜ_ : ∀ {f g} → Correct f → Correct g → Correct (f and g)
_andᶜ_ {f} {g} fᶜ gᶜ .runCorrect e = let open ≡-Reasoning in begin
  ⟦ (f and g) _ e ⟧ ≡⟨⟩
  ⟦ f _ (g _ e) ⟧  ≡⟨ fᶜ .runCorrect (g _ e) ⟩
  ⟦ g _ e ⟧         ≡⟨ gᶜ .runCorrect e ⟩
  ⟦ e ⟧              ∎

cleanup : Rule
cleanup = simplify (0* and 0+)

cleanupᶜ : Correct cleanup
cleanupᶜ = simplifyᶜ (0* and 0+) (0*ᶜ andᶜ 0+ᶜ)

_ : ∀ {a b} → cleanup _ (`add (`mul (`lit 0) (`lit a)) (`lit b)) ≡ (`lit b)
_ = refl
