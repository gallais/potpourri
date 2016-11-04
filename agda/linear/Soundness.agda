module linear.Soundness where

open import Data.Nat
open import Data.Product
open import Data.List
open import Data.Vec
open import Function
open import Algebra
open import Relation.Binary.PropositionalEquality as PEq
open ≡-Reasoning

open import linear.Type
open import linear.Context
open import linear.Usage
open import linear.Language
open import linear.Typing
open import linear.Typing.Consumption
open import linear.ILL
open import linear.Model
open import linear.Usage.Erasure
open import linear.Utils

ILL : Linear _⊢_ _⊢_
ILL = let open Monoid (monoid Type) in record
  { var   = ax
  ; app   = λ f t inc →
            let F = cut f (─oL t ax)
            in mix F (subst (_ ++_≅ _) (PEq.sym $ proj₂ identity _) inc)
  ; fst   = λ t → subst (_⊢ _) (proj₂ identity _) (cut t (&₁L ax))
  ; snd   = λ t → subst (_⊢ _) (proj₂ identity _) (cut t (&₂L ax))
  ; case  = λ t l r → mix (cut t (⊕L l r))
  ; cut   = id
  ; lam   = ─oR
  ; let'  = λ t u → mix (cut t (⊗L u))
  ; prd⊗  = λ a b → mix (⊗R a b)
  ; prd&  = &R
  ; inl   = ⊕₁R
  ; inr   = ⊕₂R
  ; neu   = id
  ; mix^I = mix
  ; mix^C = mix
  }

-- Immediate consequence: every derivation in our extension
-- gives rise to a derivation in ILL

illCheck : ∀ {γ σ t} → [[ fromList γ ]] ⊢ σ ∋ t ⊠ ]] fromList γ [[ → γ ⊢ σ
illCheck {γ} {σ} T = subst (_⊢ σ) eqγ proof where

   proof = LINEAR.linearCheck ILL T (consumptionCheck T)
   eqγ   = begin
             used (consumptionCheck T) ≡⟨ used-all (consumptionCheck T) ⟩
             toList (fromList γ)       ≡⟨ toList∘fromList γ ⟩
             γ
           ∎

illInfer : ∀ {γ σ t} → [[ fromList γ ]] ⊢ t ∈ σ ⊠ ]] fromList γ [[ → γ ⊢ σ
illInfer {γ} {σ} T = subst (_⊢ σ) eqγ proof where

   proof = LINEAR.linearInfer ILL T (consumptionInfer T)
   eqγ   = begin
             used (consumptionInfer T) ≡⟨ used-all (consumptionInfer T) ⟩
             toList (fromList γ)       ≡⟨ toList∘fromList γ ⟩
             γ
           ∎
