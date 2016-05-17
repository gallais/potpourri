module linear.Typing.Examples where

open import linear.Type
open import linear.Usage
open import linear.Language.Examples
open import linear.Typing

identityTyped : {σ : Type} → [] ⊢ σ ─o σ ∋ identity ⊠ []
identityTyped = `lam (`neu `var z)

swapTyped : {σ τ : Type} → [] ⊢ (σ ⊗ τ) ─o (τ ⊗ σ) ∋ swap ⊠ []
swapTyped = `lam (`let (`v ,, `v) ∷= `var z
                  `in `prd⊗ (`neu `var (s z)) (`neu `var z))
