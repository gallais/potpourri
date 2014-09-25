open import Data.Product hiding (map)
open import Data.Nat
open import Function

open import lib.Context as Con
open Context
open import lib.Maybe
open import lib.Nullary

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

module lps.IMLL (Pr : Set) where

  module Type where

    infixl 40 _`⊗_ _`&_
    data ty : Set where
      `κ        : (k : Pr) → ty
      _`⊗_ _`&_ : (A B : ty) → ty

  open Type
  open BelongsTo
  open Interleaving

  split-⊗ : ∀ {Γ σ τ} (pr : σ `⊗ τ ∈ Γ) → Con ty
  split-⊗ {Γ} {σ} {τ} pr = have const split actUpon Γ at pr
    where split = ε ∙ σ ∙ τ

  split-&₁ : ∀ {Γ σ τ} (pr : σ `& τ ∈ Γ) → Con ty
  split-&₁ {Γ} {σ} {τ} pr = have const split actUpon Γ at pr
    where split = ε ∙ σ

  split-&₂ : ∀ {Γ σ τ} (pr : σ `& τ ∈ Γ) → Con ty
  split-&₂ {Γ} {σ} {τ} pr = have const split actUpon Γ at pr
    where split = ε ∙ τ

  infix 3 _⊢_
  data _⊢_ : (Γ : Con ty) (σ : ty) → Set where
    `v       : ∀ {τ} → ε ∙ τ ⊢ τ
    _`⊗ˡ_    : ∀ {Γ σ τ₁ τ₂} (pr : τ₁ `⊗ τ₂ ∈ Γ) (s : split-⊗ pr ⊢ σ) → Γ ⊢ σ
    _`&ˡ₁_   : ∀ {Γ σ τ₁ τ₂} (pr : τ₁ `& τ₂ ∈ Γ) (s : split-&₁ pr ⊢ σ) → Γ ⊢ σ
    _`&ˡ₂_   : ∀ {Γ σ τ₁ τ₂} (pr : τ₁ `& τ₂ ∈ Γ) (s : split-&₂ pr ⊢ σ) → Γ ⊢ σ
    _`⊗ʳ_by_ : ∀ {Γ Δ E σ τ} (s : Δ ⊢ σ) (t : E ⊢ τ) (pr : Γ ≡ Δ ⋈ E) → Γ ⊢ σ `⊗ τ
    _`&ʳ_    : ∀ {Γ σ τ} (s : Γ ⊢ σ) (t : Γ ⊢ τ) → Γ ⊢ σ `& τ

  module Examples where

    example& : (A : ty) → ε ∙ A ⊢ A `& A
    example& A = `v `&ʳ `v

    example⊗ : (A : ty) → ε ∙ A `⊗ A ⊢ A `⊗ A
    example⊗ A = zro `⊗ˡ (`v `⊗ʳ `v by (ε ∙ʳ A ∙ˡ A))

  module RewriteRules where

    open Context.Context

    tm-assoc : (Γ Δ E : Con ty) {σ : ty} (tm : (Γ ++ Δ) ++ E ⊢ σ) →
               Γ ++ (Δ ++ E) ⊢ σ
    tm-assoc Γ Δ E {σ} = Eq.subst (flip _⊢_ σ) $ assoc++ Γ Δ E

    tm-assoc⁻¹ : (Γ Δ E : Con ty) {σ : ty} (tm : Γ ++ (Δ ++ E) ⊢ σ) →
                 (Γ ++ Δ) ++ E ⊢ σ
    tm-assoc⁻¹ Γ Δ E {σ} = Eq.subst (flip _⊢_ σ) $ Eq.sym $ assoc++ Γ Δ E

    tm-group : (Γ Δ E F : Con ty) {σ : ty} (tm : Γ ++ Δ ++ E ++ F ⊢ σ) →
               Γ ++ (Δ ++ E) ++ F ⊢ σ
    tm-group Γ Δ E F {σ} = Eq.subst (λ D → D ++ F ⊢ σ) $ assoc++ Γ Δ E