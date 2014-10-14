import lps.IMLL      as IMLL
import lps.Linearity as Linearity

open import Data.Empty
open import Data.Nat
open import Function

import lib.Context as Con
open import lib.Maybe

module lps.Linearity.Consumption (Pr : Set) where

  module Type where

    open Con.Context
    open IMLL.Type Pr

    module Cover where

      open Linearity.Type Pr

      infix 4 _≡_─_
      data _≡_─_ : {σ : ty} (S S₁ S₂ : Cover σ) → Set where
        -- structural rules
        _`⊗_     : {σ : ty} {S S₁ S₂ : Cover σ} (prσ : S ≡ S₁ ─ S₂)
                   {τ : ty} {T T₁ T₂ : Cover τ} (prτ : T ≡ T₁ ─ T₂) →
                   S `⊗ T ≡ S₁ `⊗ T₁ ─ S₂ `⊗ T₂
        [_]`⊗_   : (σ : ty) {τ : ty} {T T₁ T₂ : Cover τ} (prT : T ≡ T₁ ─ T₂) →
                   [ σ ]`⊗ T ≡ [ σ ]`⊗ T₁ ─ [ σ ]`⊗ T₂
        _`⊗[_]   : {σ : ty} {S S₁ S₂ : Cover σ} (prS : S ≡ S₁ ─ S₂) (τ : ty) →
                   S `⊗[ τ ] ≡ S₁ `⊗[ τ ] ─ S₂ `⊗[ τ ]
        [_]`&_   : (σ : ty) {τ : ty} {T T₁ T₂ : Cover τ} (prτ : T ≡ T₁ ─ T₂) →
                   [ σ ]`& T ≡ [ σ ]`& T₁ ─ [ σ ]`& T₂
        _`&[_]   : {σ : ty} {S S₁ S₂ : Cover σ} (prσ : S ≡ S₁ ─ S₂) (τ : ty) →
                   S `&[ τ ] ≡ S₁ `&[ τ ] ─ S₂ `&[ τ ]
        -- identity on the right hand side
        _`⊗ˡ_    : {σ τ : ty} {S S₁ S₂ : Cover σ} (prS : S ≡ S₁ ─ S₂)
                   (T : Cover τ) → S `⊗ T ≡ S₁ `⊗ T ─ S₂ `⊗[ τ ]
        _`⊗ʳ_    : {σ τ : ty} (S : Cover σ) {T T₁ T₂ : Cover τ}
                   (prT : T ≡ T₁ ─ T₂) → S `⊗ T ≡ S `⊗ T₁ ─ [ σ ]`⊗ T₂
        -- breaking apart free subtypes
        [_]`⊗ˡ_  : {σ : ty} (S : Cover σ) {τ : ty} (T : Cover τ) →
                   S `⊗ T ≡ [ σ ]`⊗ T ─ S `⊗[ τ ]
        [_]`⊗ˡʳ_ : {σ : ty} (S : Cover σ) {τ : ty} {T T₁ T₂ : Cover τ}
                   (prτ : T ≡ T₁ ─ T₂) → S `⊗ T ≡ [ σ ]`⊗ T₁ ─ S `⊗ T₂
        _`⊗ʳ[_]  : {σ : ty} (S : Cover σ)  {τ : ty} (T : Cover τ) →
                   S `⊗ T ≡ S `⊗[ τ ] ─ [ σ ]`⊗ T
        _`⊗ˡʳ[_] : {σ : ty} {S S₁ S₂ : Cover σ} (prσ : S ≡ S₁ ─ S₂)
                   {τ : ty} (T : Cover τ) → S `⊗ T ≡ S₁ `⊗[ τ ] ─ S₂ `⊗ T


      ¬id─ : ∀ {a} {S T : Cover a} (hf : T ≡ S ─ T) → ⊥
      ¬id─ (hf `⊗ _)      = ¬id─ hf
      ¬id─ ([ _ ]`⊗ hf)   = ¬id─ hf
      ¬id─ (hf `⊗[ _ ])   = ¬id─ hf
      ¬id─ ([ _ ]`& hf)   = ¬id─ hf
      ¬id─ (hf `&[ _ ])   = ¬id─ hf
      ¬id─ ([ _ ]`⊗ˡʳ hf) = ¬id─ hf
      ¬id─ (hf `⊗ˡʳ[ _ ]) = ¬id─ hf

      ¬diag : ∀ {a} {S T : Cover a} (hf : S ≡ T ─ T) → ⊥
      ¬diag (hf `⊗ _)    = ¬diag hf
      ¬diag ([ _ ]`⊗ hf) = ¬diag hf
      ¬diag (hf `⊗[ _ ]) = ¬diag hf
      ¬diag ([ σ ]`& hf) = ¬diag hf
      ¬diag (hf `&[ τ ]) = ¬diag hf

    module Usage where

      open Linearity.Type Pr

      data _≡_─_ {σ : ty} : (S S₁ S₂ : Usage σ) → Set where
        `idˡ : {S : Usage σ} → S ≡ S ─ [ σ ]
        `idʳ : {S : Usage σ} → S ≡ [ σ ] ─ S
        ]_[ : {S S₁ S₂ : Cover σ} (prS : S Cover.≡ S₁ ─ S₂) →
              ] S [ ≡ ] S₁ [ ─ ] S₂ [

    
      inj[_] : ∀ {a} (A : Usage a) → A ≡ [ a ] ─ A
      inj[ [ a ] ] = `idˡ
      inj[ ] A [ ] = `idʳ

      isUsed-inj : {σ : ty} {S T : Usage σ} (pr : Usage.isUsed S) →
                  (diff : S ≡ [ σ ] ─ T) → Usage.isUsed T
      isUsed-inj pr `idˡ = pr
      isUsed-inj pr `idʳ = pr

  module Context where

    open Con.Context
    open Pointwise
    open IMLL.Type Pr
    open Linearity Pr

    infix 4 _≡_─_
    data _≡_─_ : {γ : Con ty} (E Δ₁ Δ₂ : LC.Usage γ) → Set where
      ε   : ε ≡ ε ─ ε
      _∙_ : ∀ {γ σ} {Γ Δ E : LC.Usage γ} {S T U : Type.Usage σ} →
            (prΓ : Δ ≡ Γ ─ E) (prS : T Type.Usage.≡ S ─ U) →
            Δ ∙ T ≡ Γ ∙ S ─ E ∙ U

    inj[_] : ∀ {γ} (Γ : LC.Usage γ) → Γ ≡ Γ ─ LC.inj[ γ ]
    inj[_] = Pointwise.induction (λ γ Γ → Γ ≡ Γ ─ LC.inj[ γ ])
             (λ _ ih → ih ∙ Type.Usage.`idˡ) ε

    isUsed-diff : {γ : Con ty} {Γ E : LC.Usage γ} (pr : LC.isUsed Γ) →
                  (diff : Γ ≡ LC.inj[ γ ] ─ E) → LC.isUsed E
    isUsed-diff pr            ε            = pr
    isUsed-diff (pr LC.∙ prS) (diff ∙ dS) = isUsed-diff pr diff LC.∙ Type.Usage.isUsed-inj prS dS

module LCT = Type
module LCC = Context