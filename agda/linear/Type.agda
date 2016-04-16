module linear.Type where

open import Function
open import Data.Nat
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import linear.RawIso

infixr 7 _⊕_
infixr 6 _⊗_
infixr 5 _─o_
data Type : Set where
  κ    : ℕ → Type
  _⊗_  : (σ τ : Type) → Type
  _⊕_  : (σ τ : Type) → Type
  _─o_ : (σ τ : Type) → Type


-- Equality of types is decidable
κ-inj : {x y : ℕ} → κ x ≡ κ y → x ≡ y
κ-inj refl = refl

eqκ : {x y : ℕ} → RawIso (x ≡ y) (κ x ≡ κ y)
eqκ = mkRawIso (cong κ) κ-inj

⊗-inj : {σ₁ τ₁ σ₂ τ₂ : Type} → σ₁ ⊗ τ₁ ≡ σ₂ ⊗ τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
⊗-inj refl = refl , refl

eq⊗ : {σ₁ τ₁ σ₂ τ₂ : Type} →  RawIso (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) (σ₁ ⊗ τ₁ ≡ σ₂ ⊗ τ₂)
eq⊗ = mkRawIso (uncurry (cong₂ _⊗_)) ⊗-inj

⊕-inj : {σ₁ τ₁ σ₂ τ₂ : Type} → σ₁ ⊕ τ₁ ≡ σ₂ ⊕ τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
⊕-inj refl = refl , refl

eq⊕ : {σ₁ τ₁ σ₂ τ₂ : Type} →  RawIso (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) (σ₁ ⊕ τ₁ ≡ σ₂ ⊕ τ₂)
eq⊕ = mkRawIso (uncurry (cong₂ _⊕_)) ⊕-inj

─o-inj : {σ₁ τ₁ σ₂ τ₂ : Type} → σ₁ ─o τ₁ ≡ σ₂ ─o τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
─o-inj refl = refl , refl

eq─o : {σ₁ τ₁ σ₂ τ₂ : Type} →  RawIso (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) (σ₁ ─o τ₁ ≡ σ₂ ─o τ₂)
eq─o = mkRawIso (uncurry (cong₂ _─o_)) ─o-inj

eq : (σ τ : Type) → Dec (σ ≡ τ)
eq (κ x)      (κ y)      = eqκ  <$> x ≟ y
eq (σ₁ ⊗ τ₁)  (σ₂ ⊗ τ₂)  = eq⊗  <$> eq σ₁ σ₂ <*> eq τ₁ τ₂
eq (σ₁ ⊕ τ₁)  (σ₂ ⊕ τ₂)  = eq⊕  <$> eq σ₁ σ₂ <*> eq τ₁ τ₂
eq (σ₁ ─o τ₁) (σ₂ ─o τ₂) = eq─o <$> eq σ₁ σ₂ <*> eq τ₁ τ₂
eq (κ _)      (_ ⊗ _)    = no (λ ())
eq (κ _)      (_ ⊕ _)    = no (λ ())
eq (κ _)      (_ ─o _)   = no (λ ())
eq (_ ⊗ _)    (κ _)      = no (λ ())
eq (_ ⊗ _)    (_ ⊕ _)    = no (λ ())
eq (_ ⊗ _)    (_ ─o _)   = no (λ ())
eq (_ ⊕ _)    (κ _)      = no (λ ())
eq (_ ⊕ _)    (_ ⊗ _)    = no (λ ())
eq (_ ⊕ _)    (_ ─o _)   = no (λ ())
eq (_ ─o _)   (κ _)      = no (λ ())
eq (_ ─o _)   (_ ⊗ _)    = no (λ ())
eq (_ ─o _)   (_ ⊕ _)    = no (λ ())

≟-diag : (n : ℕ) → (n ≟ n) ≡ yes refl
≟-diag zero = refl
≟-diag (suc n) rewrite ≟-diag n = refl

eq-diag : (σ : Type) → eq σ σ ≡ yes refl
eq-diag (κ n)    rewrite ≟-diag n = refl
eq-diag (σ ⊗ τ)  rewrite eq-diag σ | eq-diag τ = refl
eq-diag (σ ⊕ τ)  rewrite eq-diag σ | eq-diag τ = refl
eq-diag (σ ─o τ) rewrite eq-diag σ | eq-diag τ = refl

-- Checking that a type has a given shape is decidable
data Tensor : (σ : Type) → Set where
  mkTensor : (σ τ : Type) → Tensor (σ ⊗ τ)

data Sum : (σ : Type) → Set where
  mkSum : (σ τ : Type) → Sum (σ ⊕ τ)

data Lollipop : (σ : Type) → Set where
  mkLollipop : (σ τ : Type) → Lollipop (σ ─o τ)

tensor : (σ : Type) → Dec (Tensor σ)
tensor (σ ⊗ τ)  = yes (mkTensor σ τ)
tensor (κ _)    = no (λ ())
tensor (_ ─o _) = no (λ ())
tensor (_ ⊕ _)  = no (λ ())

sum : (σ : Type) → Dec (Sum σ)
sum (σ ⊕ τ)  = yes (mkSum σ τ)
sum (κ _)    = no (λ ())
sum (_ ─o _) = no (λ ())
sum (_ ⊗ _)  = no (λ ())

lollipop : (σ : Type) → Dec (Lollipop σ)
lollipop (σ ─o τ) = yes (mkLollipop σ τ)
lollipop (κ _)    = no (λ ())
lollipop (_ ⊗ _)  = no (λ ())
lollipop (_ ⊕ _)  = no (λ ())

