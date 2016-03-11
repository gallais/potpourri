module ptt.Environment where

open import Data.Product
open import ptt.Context


infix 5 _⊨_∙_

data Env {A : Set} (θ : Context A) (R : Context A → A → Set) : (Γ : Context A) → Set where
  ε     : Env θ R ε
  _⊨_∙_ : {Γ θ₁ θ₂ : Context A} {a : A} →
          θ₁ ⋈ θ₂ ≡ θ → Env θ₁ R Γ → R θ₂ a → Env θ R (Γ ∙ a)


extend : {A : Set} {R : Context A → A → Set} (r : (a : A) → R (ε ∙ a) a)
         {θ Γ : Context A} → Env θ R Γ → (a : A) → Env (θ ∙ a) R (Γ ∙ a)
extend r ρ a = ⋈ε ∙ʳ a ⊨ ρ ∙ r a

idEnv : {A : Set} {R : Context A → A → Set} (r : (a : A) → R (ε ∙ a) a) (θ : Context A) → Env θ R θ
idEnv r ε       = ε
idEnv r (θ ∙ a) = extend r (idEnv r θ) a


split-Env : {A : Set} {R : Context A → A → Set}
            (θ Γ Γ₁ Γ₂ : Context A) → Γ₁ ⋈ Γ₂ ≡ Γ → Env θ R Γ →
            ∃ λ θ₁ → ∃ λ θ₂ → θ₁ ⋈ θ₂ ≡ θ × Env θ₁ R Γ₁ × Env θ₂ R Γ₂
split-Env θ .ε .ε .ε ε ρ = θ , ε , ⋈ε , ε , ε
split-Env θ (Γ ∙ .a) (Γ₁ ∙ .a) Γ₂ (j ∙ˡ a) (pr ⊨ ρ ∙ t) =
  let (θ₁ , θ₂ , pr₂ , ρ₁ , ρ₂) = split-Env _ Γ Γ₁ Γ₂ j ρ
      (Γ′ , p , j)              = inlineˡ pr pr₂
  in , , p , j ⊨ ρ₁ ∙ t , ρ₂
split-Env θ (Γ ∙ .a) Γ₁ (Γ₂ ∙ .a) (j ∙ʳ a) (pr ⊨ ρ ∙ t) =
  let (θ₁ , θ₂ , pr₂ , ρ₁ , ρ₂) = split-Env _ Γ Γ₁ Γ₂ j ρ
      (Γ′ , p , j)              = inlineʳ pr pr₂
  in , , p , ρ₁ , j ⊨ ρ₂ ∙ t
