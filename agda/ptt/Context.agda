module ptt.Context where

open import Function

infixl 5 _∙_
data Context (A : Set) : Set where
  ε   : Context A
  _∙_ : (Γ : Context A) (a : A) → Context A

[_] : {A : Set} (a : A) → Context A
[ a ] = ε ∙ a

-- Variable in a context
infix 1 _∈_
data _∈_ {A : Set} (a : A) : (Γ : Context A) → Set where
  z : {Γ : Context A} → a ∈ Γ ∙ a
  s : {Γ : Context A} {b : A} (m : a ∈ Γ) → a ∈ Γ ∙ b

-- Context A interleaving
infix 1 _⋈_≡_
data _⋈_≡_ {A : Set} : (Γ Δ θ : Context A) → Set where
  ε   : ε ⋈ ε ≡ ε
  _∷ˡ_ : (a : A) {Γ Δ θ : Context A} (tl : Γ ⋈ Δ ≡ θ) → Γ ∙ a ⋈ Δ     ≡ θ ∙ a
  _∷ʳ_ : (a : A) {Γ Δ θ : Context A} (tl : Γ ⋈ Δ ≡ θ) → Γ     ⋈ Δ ∙ a ≡ θ ∙ a

-- Induction principle
induction : {A : Set}
  (P : Context A → Set)
  (pε : P ε)
  (p∷  : (a : A) (Γ : Context A) → P Γ → P (Γ ∙ a)) →
  (Γ : Context A) → P Γ
induction P pε p∷ ε       = pε
induction P pε p∷ (Γ ∙ a) = p∷ a Γ (induction P pε p∷ Γ)

_++_ : {A : Set} (Γ Δ : Context A) → Context A
Γ ++ Δ = induction (λ _ → Context _) Δ (λ a _ → _∙ a) Γ

⋈ε : {A : Set} {Γ : Context A} → Γ ⋈ ε ≡ Γ
⋈ε {_} {Γ} = induction (λ Γ → Γ ⋈ ε ≡ Γ) ε (λ A _ ih → A ∷ˡ ih) Γ

ε⋈ : {A : Set} {Γ : Context A} → ε ⋈ Γ ≡ Γ
ε⋈ {_} {Γ} = induction (λ Γ → ε ⋈ Γ ≡ Γ) ε (λ A _ ih → A ∷ʳ ih) Γ

_₁⋈₂_ : {A : Set} (Γ Δ : Context A) → Γ ⋈ Δ ≡ Γ ++ Δ
Γ ₁⋈₂ Δ = induction (λ Γ → Γ ⋈ Δ ≡ Γ ++ Δ) ε⋈ (λ A _ ih → A ∷ˡ ih) Γ
