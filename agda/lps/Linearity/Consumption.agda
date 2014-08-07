import lps.IMLL      as IMLL
import lps.Linearity as Linearity

open import Data.Empty
open import Data.Nat
open import Function

import lib.Context as Con
open import lib.Maybe

module lps.Linearity.Consumption where

  module Type where

    open Con.Context
    open IMLL.Type

    module Cover where

      open Linearity.Type

      mutual

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
          [_]`⊗ˡ_  : {σ : ty} {S S₂ : Cover σ} (prσ : S ≡[ σ ]─ S₂)
                     {τ : ty} (T : Cover τ) → S `⊗ T ≡ [ σ ]`⊗ T ─ S₂ `⊗[ τ ]
          [_]`⊗ˡʳ_ : {σ : ty} {S S₂ : Cover σ} (prσ : S ≡[ σ ]─ S₂)
                     {τ : ty} {T T₁ T₂ : Cover τ} (prτ : T ≡ T₁ ─ T₂) →
                     S `⊗ T ≡ [ σ ]`⊗ T₁ ─ S₂ `⊗ T₂
          _`⊗ʳ[_]  : {σ : ty} (S : Cover σ)  {τ : ty} {T T₂ : Cover τ}
                     (prτ : T ≡[ τ ]─ T₂) → S `⊗ T ≡ S `⊗[ τ ] ─ [ σ ]`⊗ T₂
          _`⊗ˡʳ[_] : {σ : ty} {S S₁ S₂ : Cover σ} (prσ : S ≡ S₁ ─ S₂)
                     {τ : ty} {T T₂ : Cover τ} (prτ : T ≡[ τ ]─ T₂) →
                     S `⊗ T ≡ S₁ `⊗[ τ ] ─ S₂ `⊗ T₂

        infix 4 [_]─_≡_
        data [_]─_≡_ : (σ : ty) (S₂ S : Cover σ) → Set where
          `κ     : (k : ℕ) → [ `κ k ]─ `κ k ≡ `κ k
          _`⊗_   : {σ : ty} {S S₂ : Cover σ} (prσ : S ≡[ σ ]─ S₂)
                   {τ : ty} {T T₂ : Cover τ} (prτ : T ≡[ τ ]─ T₂) →
                   [ σ `⊗ τ ]─ S₂ `⊗ T₂ ≡ S `⊗ T
          [_]`⊗_ : (σ : ty) {τ : ty} {T T₂ : Cover τ} (prτ : T ≡[ τ ]─ T₂) →
                   [ σ `⊗ τ ]─ [ σ ]`⊗ T₂ ≡ [ σ ]`⊗ T
          _`⊗[_] : {σ : ty} {S S₂ : Cover σ} (prσ : S ≡[ σ ]─ S₂) (τ : ty) →
                   [ σ `⊗ τ ]─ S₂ `⊗[ τ ] ≡ S `⊗[ τ ]
          _`&_   : (σ τ : ty) → [ σ `& τ ]─ σ `& τ ≡ σ `& τ
          [_]`&_ : (σ : ty) {τ : ty} {T T₂ : Cover τ} (prT : T ≡[ τ ]─ T₂) →
                   [ σ `& τ ]─ [ σ ]`& T₂ ≡ [ σ ]`& T
          _`&[_] : {σ : ty} {S S₂ : Cover σ} (prS : S ≡[ σ ]─ S₂) (τ : ty) →
                   [ σ `& τ ]─ S₂ `&[ τ ] ≡ S `&[ τ ]

        infix 4 csyntax
        csyntax : (σ : ty) (S₂ S : Cover σ) → Set
        csyntax = [_]─_≡_
        syntax csyntax σ S₂ S = S ≡[ σ ]─ S₂

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

      inj[_] : ∀ {a} (A : Cover a) → A ≡[ a ]─ A
      inj[ `κ k      ] = `κ k
      inj[ A `⊗ B    ] = inj[ A ] `⊗ inj[ B ]
      inj[ [ a ]`⊗ B ] = [ a ]`⊗ inj[ B ]
      inj[ A `⊗[ b ] ] = inj[ A ] `⊗[ b ]
      inj[ a `& b    ] = a `& b
      inj[ A `&[ b ] ] = inj[ A ] `&[ b ]
      inj[ [ a ]`& B ] = [ a ]`& inj[ B ]

    module Usage where

      open Linearity.Type

      data _≡_─_ {σ : ty} : (S S₁ S₂ : Usage σ) → Set where
        `id : {S : Usage σ} → S ≡ S ─ [ σ ]
        ]_[ : {S S₁ S₂ : Cover σ} (prS : S Cover.≡ S₁ ─ S₂) →
              ] S [ ≡ ] S₁ [ ─ ] S₂ [
        [_] : {S S₂ : Cover σ} (prS : S Cover.≡[ σ ]─ S₂) → ] S [ ≡ [ σ ] ─ ] S₂ [

    
      inj[_] : ∀ {a} (A : Usage a) → A ≡ [ a ] ─ A
      inj[ [ a ] ] = `id
      inj[ ] A [ ] = [ Cover.inj[ A ] ]

  module Context where

    open Con.Context
    open Pointwise
    open IMLL.Type
    open Linearity

    infix 4 _≡_─_
    data _≡_─_ : {γ : Con ty} (E Δ₁ Δ₂ : LC.Usage γ) → Set where
      ε   : ε ≡ ε ─ ε
      _∙_ : ∀ {γ σ} {Γ Δ E : LC.Usage γ} {S T U : Type.Usage σ} →
            (prΓ : Δ ≡ Γ ─ E) (prS : T Type.Usage.≡ S ─ U) →
            Δ ∙ T ≡ Γ ∙ S ─ E ∙ U

    inj[_] : ∀ {γ} (Γ : LC.Usage γ) → Γ ≡ Γ ─ LC.inj[ γ ]
    inj[_] = Pointwise.induction (λ γ Γ → Γ ≡ Γ ─ LC.inj[ γ ])
             (λ _ ih → ih ∙ Type.Usage.`id) ε

module LCT = Type
module LCC = Context
