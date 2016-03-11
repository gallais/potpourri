module ptt.Context where

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

infixl 10 _∙_
data Context (A : Set) : Set where
  ε   : Context A
  _∙_ : (Γ : Context A) (a : A) → Context A

-- Variable in a context
infix 1 _∈_
data _∈_ {A : Set} (a : A) : (Γ : Context A) → Set where
  z : {Γ : Context A} → a ∈ Γ ∙ a
  s : {Γ : Context A} {b : A} (m : a ∈ Γ) → a ∈ Γ ∙ b

-- Context A interleaving
infix 5 _⋈_≡_
infixl 10 _∙ˡ_ _∙ʳ_
data _⋈_≡_ {A : Set} : (Γ Δ θ : Context A) → Set where
  ε   : ε ⋈ ε ≡ ε
  _∙ˡ_ : {Γ Δ θ : Context A} (tl : Γ ⋈ Δ ≡ θ) (a : A) → Γ ∙ a ⋈ Δ     ≡ θ ∙ a
  _∙ʳ_ : {Γ Δ θ : Context A} (tl : Γ ⋈ Δ ≡ θ) (a : A) → Γ     ⋈ Δ ∙ a ≡ θ ∙ a

symmetry : {A : Set} {Γ Δ θ : Context A} → Γ ⋈ Δ ≡ θ → Δ ⋈ Γ ≡ θ
symmetry ε         = ε
symmetry (pr ∙ˡ a) = symmetry pr ∙ʳ a
symmetry (pr ∙ʳ a) = symmetry pr ∙ˡ a

inlineˡ : {A : Set} {Γ Δ θ Γ₁ Γ₂ : Context A} → Γ ⋈ Δ ≡ θ → Γ₁ ⋈ Γ₂ ≡ Γ →
        ∃ λ Γ′ → Γ′ ⋈ Γ₂ ≡ θ × Γ₁ ⋈ Δ ≡ Γ′
inlineˡ ε        ε         = ε , ε , ε
inlineˡ (p ∙ˡ a) (j ∙ˡ .a) = let (Γ′ , p′ , j′) = inlineˡ p j in Γ′ ∙ a , p′ ∙ˡ a , j′ ∙ˡ a
inlineˡ (p ∙ˡ a) (j ∙ʳ .a) = let (Γ′ , p′ , j′) = inlineˡ p j in Γ′     , p′ ∙ʳ a , j′
inlineˡ (p ∙ʳ a) j         = let (Γ′ , p′ , j′) = inlineˡ p j in Γ′ ∙ a , p′ ∙ˡ a , j′ ∙ʳ a
        
inlineʳ : {A : Set} {Γ Δ θ Γ₁ Γ₂ : Context A} → Γ ⋈ Δ ≡ θ → Γ₁ ⋈ Γ₂ ≡ Γ →
        ∃ λ Γ′ → Γ₁ ⋈ Γ′ ≡ θ × Γ₂ ⋈ Δ ≡ Γ′
inlineʳ ε        ε         = ε , ε , ε
inlineʳ (p ∙ʳ a) j         = let (Γ′ , p′ , j′) = inlineʳ p j in Γ′ ∙ a , p′ ∙ʳ a , j′ ∙ʳ a
inlineʳ (p ∙ˡ a) (j ∙ˡ .a) = let (Γ′ , p′ , j′) = inlineʳ p j in Γ′     , p′ ∙ˡ a , j′
inlineʳ (p ∙ˡ a) (j ∙ʳ .a) = let (Γ′ , p′ , j′) = inlineʳ p j in Γ′ ∙ a , p′ ∙ʳ a , j′ ∙ˡ a

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
⋈ε {_} {Γ} = induction (λ Γ → Γ ⋈ ε ≡ Γ) ε (λ A _ ih → ih ∙ˡ A) Γ

ε⋈ : {A : Set} {Γ : Context A} → ε ⋈ Γ ≡ Γ
ε⋈ {_} {Γ} = induction (λ Γ → ε ⋈ Γ ≡ Γ) ε (λ A _ ih → ih ∙ʳ A) Γ

_₁⋈₂_ : {A : Set} (Γ Δ : Context A) → Γ ⋈ Δ ≡ Γ ++ Δ
Γ ₁⋈₂ Δ = induction (λ Γ → Γ ⋈ Δ ≡ Γ ++ Δ) ε⋈ (λ A _ ih → ih ∙ˡ A) Γ

-- Properties of inline
inlineʳ-⋈ε : {A : Set} {Γ Δ θ : Context A} (inc : Γ ⋈ Δ ≡ θ) →
             inlineʳ inc ⋈ε ≡ (Δ , inc , ε⋈)
inlineʳ-⋈ε ε          = refl
inlineʳ-⋈ε (inc ∙ˡ a) with inlineʳ inc ⋈ε | inlineʳ-⋈ε inc
inlineʳ-⋈ε (inc ∙ˡ a) | Δ , .inc , ._ | refl = refl
inlineʳ-⋈ε (inc ∙ʳ a) with inlineʳ inc ⋈ε | inlineʳ-⋈ε inc
... | Δ , .inc , ._ | refl = refl
