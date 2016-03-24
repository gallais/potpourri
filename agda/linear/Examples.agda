module linear.Examples where

open import Data.Nat
open import Data.Fin

open import linear.Type
open import linear.Context
open import linear.Usage
open import linear.Language
open import linear.Typing

var : {n : ℕ} {γ : Context n} {σ : Type} {Γ Δ : Usages γ} {k : Fin n} →
      Γ ⊢ k ∈[ σ ]⊠ Δ → Γ ⊢ σ ∋ `neu `var k ⊠ Δ
var v = `neu `var v

⊢swap⊗ : {σ τ : Type} → [] ⊢ (σ ⊗ τ) ─o (τ ⊗ σ) ∋ _ ⊠ []
⊢swap⊗ =
  `lam `let (`v ,, `v) ∷= `var z `in
       `prd (var (s z)) (var z)

⊗⊕-distr : (σ τ ν : Type) → [] ⊢ (σ ⊗ (τ ⊕ ν)) ─o (σ ⊗ τ) ⊕ (σ ⊗ ν) ∋ _ ⊠ []
⊗⊕-distr σ τ ν =
  `lam `let (`v ,, `v) ∷= `var z `in
       `neu `case `var (s z) return (σ ⊗ τ) ⊕ (σ ⊗ ν)
            of `inl (`prd (var (s z)) (var z))
            %% `inr (`prd (var (s z)) (var z))
