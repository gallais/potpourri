module ptt.Usage where

open import ptt.Context

data Usage {A : Set} : (a : A) → Set where
  [_] : (a : A) → Usage a
  ]_[ : (a : A) → Usage a

infixl 10 _∙_
data Usages {A : Set} : (γ : Context A) → Set where
  ε   : Usages ε
  _∙_ : {γ : Context A} {a : A} → Usages γ → Usage a → Usages (γ ∙ a)

[[_]] : {A : Set} (γ : Context A) → Usages γ
[[_]] = induction Usages ε (λ a Γ ih → ih ∙ [ a ])

]]_[[ : {A : Set} (γ : Context A) → Usages γ
]]_[[ = induction Usages ε (λ a Γ ih → ih ∙ ] a [)

infix 1 _∋_⊠_
data _∋_⊠_ {A : Set} : {γ : Context A} (Γ : Usages γ) (a : A) (Δ : Usages γ) → Set where
  z : {γ : Context A} {Γ : Usages γ} {a : A} → Γ ∙ [ a ] ∋ a ⊠ Γ ∙ ] a [
  s : {γ : Context A} {Γ Δ : Usages γ} {a b : A} {u : Usage b} →
      Γ ∋ a ⊠ Δ → Γ ∙ u ∋ a ⊠ Δ ∙ u
