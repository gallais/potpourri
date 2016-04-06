module linear.Typing.Functional where

open import Data.Nat
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import linear.Type
open import linear.Context
open import linear.Language
open import linear.Usage
open import linear.Usage.Functional
open import linear.Typing
open import linear.Relation.Functional

RPattern : (i : Type × Σ[ m ∈ ℕ ] Pattern m) (o : let (_ , m , _) = i in Context m) → Set
RPattern (A , _ , p) δ = A ∋ p ↝ δ

functionalPattern : Functional′ RPattern
functionalPattern _ `v         `v         = refl
functionalPattern _ (p₁ ,, q₁) (p₂ ,, q₂) = cong₂ _ (functionalPattern _ p₁ p₂) (functionalPattern _ q₁ q₂)

functionalInfer : Functional (InferTyping TInfer)
functionalInfer _ (`var k₁)    (`var k₂)    = functionalFin _ k₁ k₂
functionalInfer _ (`app t₁ u₁) (`app t₂ u₂) = cong (λ { (_ ─o τ) → τ; σ → σ }) $ functionalInfer _ t₁ t₂
functionalInfer _ (`case t₁ return σ₁ of l₁ %% r₁) (`case t₂ return .σ₁ of l₂ %% r₂) = refl
functionalInfer _ (`cut t₁) (`cut t₂) = refl


mutual

  functionalInferPost : Functional′ (InferTypingPost TInfer)
  functionalInferPost _ (`var x₁)    (`var x₂) = functionalFinPost _ x₁ x₂
  functionalInferPost _ (`app t₁ u₁) (`app t₂ u₂)
    with functionalInferPost _ t₁ t₂
  ... | refl = cong _ $ functionalCheckPost _ u₁ u₂
  functionalInferPost _ (`case t₁ return σ₁ of l₁ %% r₁) (`case t₂ return .σ₁ of l₂ %% r₂)
    with functionalInferPost _ t₁ t₂
  ... | refl with functionalCheckPost _ l₁ l₂
  ... | refl = refl
  functionalInferPost _ (`cut t₁) (`cut t₂) = cong _ $ functionalCheckPost _ t₁ t₂

  functionalCheckPost  : Functional′ (CheckTypingPost TCheck)
  functionalCheckPost _ (`lam t₁) (`lam t₂)
    with functionalCheckPost _ t₁ t₂
  ... | refl = refl
  functionalCheckPost (n , γ , Γ , σ , `let p ∷= t `in u) 
    (`let_∷=_`in_ {δ = δ} p₁ t₁ u₁) (`let p₂ ∷= t₂ `in u₂)
    with functionalInferPost _ t₁ t₂
  ... | refl with functionalPattern _ p₁ p₂
  ... | refl = functional++ ]] δ [[ refl (functionalCheckPost _ u₁ u₂)
  functionalCheckPost _ (`prd a₁ b₁) (`prd a₂ b₂)
    with functionalCheckPost _ a₁ a₂
  ... | refl = functionalCheckPost _ b₁ b₂
  functionalCheckPost _ (`inl t₁) (`inl t₂) = functionalCheckPost _ t₁ t₂
  functionalCheckPost _ (`inr t₁) (`inr t₂) = functionalCheckPost _ t₁ t₂
  functionalCheckPost _ (`neu t₁) (`neu t₂) = cong proj₂ $ functionalInferPost _ t₁ t₂

mutual

  functionalInferPre : Functional′ (InferTypingPre TInfer)
  functionalInferPre _ (`var k₁)    (`var k₂)    = functionalFinPre _ k₁ k₂
  functionalInferPre _ (`app t₁ u₁) (`app t₂ u₂)
    with functionalInfer _ t₁ t₂
  ... | refl with functionalCheckPre _ u₁ u₂
  ... | refl with functionalInferPre _ t₁ t₂
  ... | refl = refl
  functionalInferPre _ (`case t₁ return σ of l₁ %% r₁) (`case t₂ return .σ of l₂ %% r₂)
    with functionalInfer _ t₁ t₂
  ... | refl with functionalCheckPre _ r₁ r₂
  ... | refl with functionalInferPre _ t₁ t₂
  ... | refl = refl
  functionalInferPre _ (`cut t₁) (`cut t₂) = cong _ $ functionalCheckPre _ t₁ t₂

  functionalCheckPre : Functional′ (CheckTypingPre TCheck)
  functionalCheckPre _ (`lam t₁) (`lam t₂) with functionalCheckPre _ t₁ t₂
  ... | refl = refl
  functionalCheckPre _ (`let p₁ ∷= t₁ `in u₁) (`let p₂ ∷= t₂ `in u₂)
    with functionalInfer _ t₁ t₂
  ... | refl with functionalPattern _ p₁ p₂
  ... | refl with functional++ [[ patternContext p₁ ]] refl (functionalCheckPre _ u₁ u₂)
  ... | refl = cong proj₂ $ functionalInferPre _ t₁ t₂
  functionalCheckPre _ (`prd a₁ b₁) (`prd a₂ b₂) rewrite functionalCheckPre _ b₁ b₂ = functionalCheckPre _ a₁ a₂
  functionalCheckPre _ (`inl t₁) (`inl t₂) = functionalCheckPre _ t₁ t₂
  functionalCheckPre _ (`inr t₁) (`inr t₂) = functionalCheckPre _ t₁ t₂
  functionalCheckPre _ (`neu t₁) (`neu t₂) = cong proj₂ $ functionalInferPre _ t₁ t₂
