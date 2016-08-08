module monoid.Utils where

open import Level
open import Data.Nat
open import Data.Fin

infixr 5 _⟶_ _⟶′_
_⟶_ : {ℓ^A ℓ^F ℓ^G : Level} {A : Set ℓ^A} (F : A → Set ℓ^F) (G : A → Set ℓ^G) → Set _
F ⟶ G = ∀ {a} → F a → G a

_⟶′_ : {ℓ^A ℓ^F ℓ^G : Level} {A : Set ℓ^A} (F : A → Set ℓ^F) (G : A → Set ℓ^G) → A → Set _
F ⟶′ G = λ a → F a → G a

record Values {ℓ} (A : ℕ → Set ℓ) (n : ℕ) : Set ℓ where
  constructor pack
  field lookup : Fin n → A n
open Values public
