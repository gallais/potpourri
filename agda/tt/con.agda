module tt.con where

open import Data.Unit
open import Data.Product
open import Data.Nat

-- Contexts

infixl 5 _∙⟩_
data Context (E : ℕ → Set) : ℕ → Set where
  ⟨⟩   : Context E 0
  _∙⟩_ : {n : ℕ} → Context E n → E n → Context E (suc n)

_⇒_ : (E F : ℕ → Set) → Set
E ⇒ F = {n : ℕ} → E n → F n

cmap : {E F : ℕ → Set} (f : E ⇒ F) → Context E ⇒ Context F
cmap f ⟨⟩       = ⟨⟩
cmap f (Γ ∙⟩ e) = cmap f Γ ∙⟩ f e

IRel : {A : Set} (E : A → Set) → Set₁
IRel {A} E = {a : A} (e f : E a) → Set

record IEquivalence {A : Set} (E : A → Set) (R : IRel E) : Set where
  field
    irefl  : {a : A} {e : E a} → R e e
    isym   : {a : A} {e f : E a} → R e f → R f e
    itrans : {a : A} {e f g : E a} → R e f → R f g → R e g

infix 3 _[_]_
_[_]_ : {E : ℕ → Set} {m : ℕ} (Γ : Context E m) (R : IRel E) (Δ : Context E m) → Set
⟨⟩     [ R ] ⟨⟩     = ⊤
Γ ∙⟩ γ [ R ] Δ ∙⟩ δ = Γ [ R ] Δ × R γ δ

pure : {E : ℕ → Set} {m : ℕ} (Γ : Context E m) {R : IRel E} (prf : {m : ℕ} (γ : E m) → R γ γ) → Γ [ R ] Γ
pure ⟨⟩       prf = tt
pure (Γ ∙⟩ γ) prf = pure Γ prf , prf γ
