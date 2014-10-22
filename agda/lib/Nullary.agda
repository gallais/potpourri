module lib.Nullary where

open import Relation.Nullary

open import Function
open import Data.Unit
open import Data.Empty

dec : ∀ {ℓᵖ ℓᶜ} {P : Set ℓᵖ} {C : Set ℓᶜ} (d : Dec P) (yes : P → C) (no : ¬ P → C) → C
dec (yes p) y n = y p
dec (no ¬p) y n = n ¬p

dec′ : ∀ {ℓᵖ ℓᶜ} {P : Set ℓᵖ} (C : Dec P → Set ℓᶜ)
      (d : Dec P) (yes : (p : P) → C (yes p)) (no : (¬p : ¬ P) → C (no ¬p)) → C d
dec′ C (yes p) y n = y p
dec′ C (no ¬p) y n = n ¬p


tactics : ∀ {ℓᵃ ℓᵖ} {A : Set ℓᵃ} {P : A → Set ℓᵖ} (P? : (a : A) → Dec $ P a) →
          (a : A) {_ : dec (P? a) (const ⊤) (const ⊥)} → P a
tactics {ℓᵖ = ℓᵖ} {P = P} P? a {pr} = dec′ C (P? a) const (const ⊥-elim) pr
  where C : Dec $ P a → Set ℓᵖ
        C Pa? = dec Pa? (const ⊤) (const ⊥) → P a