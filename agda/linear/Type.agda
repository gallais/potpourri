module linear.Type where

open import Data.Nat

infixr 7 _⊕_
infixr 6 _⊗_
infixr 5 _─o_
data Type : Set where
  κ    : ℕ → Type
  _⊗_  : (σ τ : Type) → Type
  _⊕_  : (σ τ : Type) → Type
  _─o_ : (σ τ : Type) → Type
