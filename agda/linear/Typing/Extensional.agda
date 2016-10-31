module linear.Typing.Extensional where

open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality as PEq

open import linear.Type
open import linear.Context
open import linear.Context.Pointwise as CP
open import linear.Usage
open import linear.Usage.Pointwise as UP
open import linear.Typing

Extensional : {T : ℕ → Set} (𝓣 : Typing T) → Set
Extensional {T} 𝓣 =
 {k : ℕ} {γ δ : Context k}  (eqs₁ : Context[ _≡_ ] δ γ) (eqs₂ : Context[ _≡_ ] γ δ)
 {Γ Δ : Usages γ} {Γ′ Δ′ : Usages δ}
 (EQs₁ : Usages[ _≡_ , UsageEq ] eqs₁ Γ′ Γ) (EQs₂ : Usages[ _≡_ , UsageEq ] eqs₂ Δ Δ′)
 {rt : T k} {σ : Type} (t : 𝓣 Γ rt σ Δ) → 𝓣 Γ′ rt σ Δ′

extensionalFin : Extensional TFin
extensionalFin
  (PEq.refl ∷ eqs₁) (PEq.refl ∷ eqs₂)
  (PEq.refl ∷ EQs₁) (PEq.refl ∷ EQs₂) z
  with CP.pointwiseEq (CP.trans eqs₁ eqs₂)
     | UP.pointwiseEq (UP.trans EQs₁ EQs₂)
... | PEq.refl | PEq.refl = z
extensionalFin
  (PEq.refl ∷ eqs₁) (PEq.refl ∷ eqs₂)
  (PEq.refl ∷ EQs₁) (PEq.refl ∷ EQs₂) (s k) =
  s extensionalFin eqs₁ eqs₂ EQs₁ EQs₂ k


mutual

  extensionalInfer : Extensional TInfer
  extensionalInfer eqs₁ eqs₂ EQs₁ EQs₂ (`var k) =
    `var extensionalFin eqs₁ eqs₂ EQs₁ EQs₂ k
  extensionalInfer eqs₁ eqs₂ EQs₁ EQs₂ (`app f t) =
    let f′ = extensionalInfer eqs₁ eqs₂ EQs₁ (coerceʳ eqs₂) f
        t′ = extensionalCheck (CP.sym eqs₂) eqs₂ (coerceˡ eqs₂) EQs₂ t
    in `app f′ t′
  extensionalInfer eqs₁ eqs₂ EQs₁ EQs₂ (`fst t) =
    `fst (extensionalInfer eqs₁ eqs₂ EQs₁ EQs₂ t)
  extensionalInfer eqs₁ eqs₂ EQs₁ EQs₂ (`snd t) =
    `snd (extensionalInfer eqs₁ eqs₂ EQs₁ EQs₂ t)
  extensionalInfer eqs₁ eqs₂ EQs₁ EQs₂ (`case t return σ of l %% r) =
    let t′ = extensionalInfer eqs₁ eqs₂ EQs₁ (coerceʳ eqs₂) t
        l′ = extensionalCheck (PEq.refl ∷ CP.sym eqs₂) (PEq.refl ∷ eqs₂)
                              (PEq.refl ∷ coerceˡ eqs₂) (PEq.refl ∷ EQs₂) l
        r′ = extensionalCheck (PEq.refl ∷ CP.sym eqs₂) (PEq.refl ∷ eqs₂)
                              (PEq.refl ∷ coerceˡ eqs₂) (PEq.refl ∷ EQs₂) r
    in `case t′ return σ of l′ %% r′
  extensionalInfer eqs₁ eqs₂ EQs₁ EQs₂ (`cut t) =
    `cut $ extensionalCheck eqs₁ eqs₂ EQs₁ EQs₂ t

  extensionalCheck : Extensional TCheck
  extensionalCheck eqs₁ eqs₂ EQs₁ EQs₂ (`lam t) =
    `lam extensionalCheck (PEq.refl ∷ eqs₁) (PEq.refl ∷ eqs₂)
                         (PEq.refl ∷ EQs₁ ) (PEq.refl ∷ EQs₂) t
  extensionalCheck eqs₁ eqs₂ EQs₁ EQs₂ (`let p ∷= t `in u) =
    let t′ = extensionalInfer eqs₁ eqs₂ EQs₁ (coerceʳ eqs₂) t
        δ  = patternContext p
        u′ = extensionalCheck
               (CP.refl {γ = δ} CP.++ CP.sym eqs₂) (CP.refl {γ = δ} CP.++ eqs₂)
               (UP.refl {Γ = [[ δ ]]} UP.++ coerceˡ eqs₂) (UP.refl {Γ = ]] δ [[} UP.++ EQs₂)
               u
    in `let p ∷= t′ `in u′
  extensionalCheck eqs₁ eqs₂ EQs₁ EQs₂ (`prd⊗ a b) =
    let a′ = extensionalCheck eqs₁ eqs₂ EQs₁ (coerceʳ eqs₂) a
        b′ = extensionalCheck (CP.sym eqs₂) eqs₂ (coerceˡ eqs₂) EQs₂ b
    in `prd⊗ a′ b′
  extensionalCheck eqs₁ eqs₂ EQs₁ EQs₂ (`prd& a b) =
    `prd& (extensionalCheck eqs₁ eqs₂ EQs₁ EQs₂ a) (extensionalCheck eqs₁ eqs₂ EQs₁ EQs₂ b)
  extensionalCheck eqs₁ eqs₂ EQs₁ EQs₂ (`inl t) =
    `inl extensionalCheck eqs₁ eqs₂ EQs₁ EQs₂ t
  extensionalCheck eqs₁ eqs₂ EQs₁ EQs₂ (`inr t) =
    `inr extensionalCheck eqs₁ eqs₂ EQs₁ EQs₂ t
  extensionalCheck eqs₁ eqs₂ EQs₁ EQs₂ (`neu t) =
    `neu extensionalInfer eqs₁ eqs₂ EQs₁ EQs₂ t
