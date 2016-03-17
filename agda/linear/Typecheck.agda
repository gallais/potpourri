module linear.Typecheck where

open import Function
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import linear.Type
open import linear.Context
open import linear.Usage
open import linear.Language
open import linear.RawIso

CONSUME : {n : ℕ} {γ : Context n} (Γ : Usages γ) (k : Fin n) → Set
CONSUME Γ k = ∃₂ λ σ Δ → Γ ⊢ k ∈[ σ ]⊠ Δ

INFER : {n : ℕ} {γ : Context n} (Γ : Usages γ) (t : Infer n) → Set
INFER Γ t = ∃₂ λ σ Δ → Γ ⊢ t ∈ σ ⊠ Δ

CHECK : {n : ℕ} {γ : Context n} (Γ : Usages γ) (σ : Type) (t : Check n) → Set
CHECK Γ σ t = ∃ λ Δ → Γ ⊢ σ ∋ t ⊠ Δ

consumeSuc : {n : ℕ} {γ : Context n} (Γ : Usages γ) {σ : Type} (a : Usage σ) (k : Fin n) →
             RawIso (CONSUME Γ k) (CONSUME (a ∷ Γ) (suc k))
push (consumeSuc Γ a k) (σ , Δ        , v)     = σ , (a ∷ Δ) , s v
pull (consumeSuc Γ a k) (σ , (.a ∷ Δ) , (s v)) = σ , Δ , v

inferVar : {n : ℕ} {γ : Context n} (Γ : Usages γ) (k : Fin n) → RawIso (CONSUME Γ k) (INFER Γ (`var k))
push (inferVar Γ k) (σ , Δ , v)      = σ , Δ , `var v
pull (inferVar Γ k) (σ , Δ , `var v) = σ , Δ , v

inferCut : {n : ℕ} {γ : Context n} (Γ : Usages γ) (t : Check n) (σ : Type) →
           RawIso (CHECK Γ σ t) (INFER Γ (`cut t σ))
push (inferCut Γ t σ) (Δ , p)           = σ , Δ , `cut p
pull (inferCut Γ t σ) (.σ , Δ , `cut p) = Δ , p

-- Decidability of Type-checking

consume : {n : ℕ} {γ : Context n} (Γ : Usages γ) (k : Fin n) → Dec $ CONSUME Γ k
consume ([ σ ] ∷ Γ) zero    = yes (σ , ] σ [ ∷ Γ , z)
consume (] σ [ ∷ Γ) zero    = no (λ { (_ , _ , ()) })
consume (σ ∷ Γ)     (suc k) = consumeSuc Γ σ k <$> consume Γ k

mutual

  infer : {n : ℕ} {γ : Context n} (Γ : Usages γ) (t : Infer n) → Dec $ INFER Γ t
  infer Γ (`var k)                     = inferVar Γ k <$> consume Γ k
  infer Γ (`app t u)                   = {!!}
  infer Γ (`case t return ν of l %% r) = {!!}
  infer Γ (`cut t σ)                   = inferCut Γ t σ <$> check Γ σ t

  check : {n : ℕ} {γ : Context n} (Γ : Usages γ) (σ : Type) (t : Check n) → Dec $ CHECK Γ σ t

  -- LAMBDA ABSTRACTION
  check Γ σ (`lam b)
    with lollipop σ
  ... | no _ = no {!!}
  check Γ .(σ ─o τ) (`lam b)
      | yes (mkLollipop σ τ)
    with check ([ σ ] ∷ Γ) τ b
  ... | no ¬p                = no {!!}
  ... | yes ([ .σ ] ∷ Δ , p) = no {!!}
  ... | yes (] .σ [ ∷ Δ , p) = yes (Δ , `lam p)

  check Γ σ (`let p ∷= t `in u) = {!!}
  check Γ σ (`prd t u)          = {!!}
  check Γ σ (`inl t)            = {!!}
  check Γ σ (`inr t)            = {!!}

  check Γ σ (`neu t)
    with infer Γ t
  ... | no ¬p = {!!}
  ... | yes (τ , Δ , p)
    with eq σ τ
  ... | no ¬σ≡τ = no {!!}
  check Γ σ (`neu t) | yes (.σ , Δ , p) | yes refl = yes (Δ , `neu p)
