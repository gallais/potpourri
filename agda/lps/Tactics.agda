module lps.Tactics where

open import Prelude
open import Bag-equivalence
open import Equality.Propositional

import Relation.Nullary as RN
import Relation.Binary.PropositionalEquality as RBEq
open import lib.Maybe

module Tactics (Pr : Set) (_≟_ : (x y : Pr) → RN.Dec (x RBEq.≡ y)) where

  open import lib.Context
  open Context
  module BT = BelongsTo
  module Il = Interleaving

  open import lps.IMLL Pr
  open Type
  open Pointwise

  toContext : List Pr → Con ty
  toContext = foldr (λ p Γ → Γ ∙ `κ p) ε

  toGoal : Pr → List Pr → ty
  toGoal p = foldr (λ p σ → σ `⊗ `κ p) $ `κ p

  data isProduct : (σ : ty) → Set where
    `κ   : (p : Pr) → isProduct $ `κ p
    _`⊗_ : {σ τ : ty} (S : isProduct σ) (T : isProduct τ) → isProduct $ σ `⊗ τ

  isProductToGoal : (x : Pr) (xs : List Pr) → isProduct $ toGoal x xs
  isProductToGoal x []       = `κ x
  isProductToGoal x (y ∷ xs) = isProductToGoal x xs `⊗ `κ y

  fromProduct : {σ : ty} (S : isProduct σ) → List Pr
  fromProduct (`κ p)   = p ∷ []
  fromProduct (S `⊗ T) = fromProduct S ++ fromProduct T

  isProducts : (Γ : Con ty) → Set
  isProducts = PCon isProduct

  isProductsToContext : (xs : List Pr) → isProducts $ toContext xs
  isProductsToContext []       = ε
  isProductsToContext (x ∷ xs) = isProductsToContext xs ∙ `κ x

  fromProducts : {γ : Con ty} (Γ : isProducts γ) → List Pr
  fromProducts ε       = []
  fromProducts (Γ ∙ S) = fromProducts Γ ++ fromProduct S

  noWiths : {γ : Con ty} {σ τ : ty} (Γ : isProducts γ) (var : σ `& τ BT.∈ γ) → ⊥ {lzero}
  noWiths (Γ ∙ ()) BT.zro
  noWiths (Γ ∙ _)  (BT.suc var) = noWiths Γ var

  isProducts-split : {γ : Con ty} {σ τ : ty} (Γ : isProducts γ) (var : σ `⊗ τ BT.∈ γ) →
                     isProducts $ split-⊗ var
  isProducts-split (Γ ∙ S `⊗ T) BT.zro      = Γ ∙ S ∙ T
  isProducts-split (Γ ∙ S)     (BT.suc var) = isProducts-split Γ var ∙ S

  isProducts-merge⁻¹ : {γ δ e : Con ty} (Γ : isProducts γ) (mg : γ Interleaving.≡ δ ⋈ e) →
                       isProducts δ × isProducts e
  isProducts-merge⁻¹ ε       Il.ε         = ε , ε
  isProducts-merge⁻¹ (Γ ∙ S) (mg Il.∙ʳ σ) = Σ-map id (λ E → E ∙ S) $ isProducts-merge⁻¹ Γ mg
  isProducts-merge⁻¹ (Γ ∙ S) (mg Il.∙ˡ σ) = Σ-map (λ Δ → Δ ∙ S) id $ isProducts-merge⁻¹ Γ mg

  open import Function-universe equality-with-J as Function-universe

  isProduct↔ : {σ : ty} (S T : isProduct σ) → fromProduct S ≈-bag fromProduct T
  isProduct↔ (`κ p)     (`κ .p)    = ≈″⇒≈ (p ∷ [])
  isProduct↔ (S₁ `⊗ T₁) (S₂ `⊗ T₂) = ++-cong (isProduct↔ S₁ S₂) (isProduct↔ T₁ T₂)

  isProducts↔ : {γ : Con ty} (Γ Δ : isProducts γ) → fromProducts Γ ≈-bag fromProducts Δ
  isProducts↔ ε        ε        = ≈″⇒≈ []
  isProducts↔ (Γ ∙ S₁) (Δ ∙ S₂) = ++-cong (isProducts↔ Γ Δ) (isProduct↔ S₁ S₂)

  isProducts⋈↔ : {γ δ e : Con ty} (Γ : isProducts γ) (Δ : isProducts δ) (E : isProducts e)
                 (mg : γ Interleaving.≡ δ ⋈ e) →
                 fromProducts Γ ≈-bag fromProducts Δ ++ fromProducts E
  isProducts⋈↔ ε        ε        ε        Il.ε         = ≈″⇒≈ []
  isProducts⋈↔ (Γ ∙ S₁) Δ        (E ∙ S₂) (mg Il.∙ʳ σ) = λ z →
    z ∈ fromProducts (Γ ∙ S₁) ↔⟨ ++-cong (isProducts⋈↔ Γ Δ E mg) (isProduct↔ S₁ S₂) z ⟩
   {!!}
  isProducts⋈↔ (Γ ∙ S₁) (Δ ∙ S₂) E        (mg Il.∙ˡ σ) = λ z →
    z ∈ fromProducts (Γ ∙ S₁) ↔⟨ ++-cong (isProducts⋈↔ Γ Δ E mg) (isProduct↔ S₁ S₂) z ⟩
    {!!}

  split↔ : {γ : Con ty} {σ τ : ty} (Γ : isProducts γ) (var : σ `⊗ τ BT.∈ γ) →
           fromProducts Γ ≈-bag fromProducts (isProducts-split Γ var)
  split↔ (Γ ∙ S `⊗ T) BT.zro       = λ z → {!!}
{-
    {!!} ↔⟨ Any-++ (_≡_ z) (fromProducts Γ) (fromProduct S ++ fromProduct T) ⟩
    {!!} ↔⟨ ≡⇒↝ bijection refl ⊎-cong Any-++ (_≡_ z) (fromProduct S) (fromProduct T) ⟩
    {!!}
-}
  split↔ (Γ ∙ S)      (BT.suc var) = {!!}

  sound : {γ : Con ty} {σ : ty} (Γ : isProducts γ) (S : isProduct σ) →
          γ ⊢ σ → fromProducts Γ ≈-bag fromProduct S
  sound (ε ∙ S) T        `v                  = isProduct↔ S T
  sound Γ       S        (var `⊗ˡ tm)        =
    let ih = sound (isProducts-split Γ var) S tm
    in λ z →
       z ∈ fromProducts Γ                        ↔⟨ split↔ Γ var z ⟩
       z ∈ fromProducts (isProducts-split Γ var) ↔⟨ ih z ⟩
       z ∈ fromProduct S □
  sound Γ       (S `⊗ T) (tm₁ `⊗ʳ tm₂ by mg) =
    let (Δ , E) = isProducts-merge⁻¹ Γ mg
        ih₁     = sound Δ S tm₁
        ih₂     = sound E T tm₂
    in λ z →
      z ∈ fromProducts Γ                   ↔⟨ isProducts⋈↔ Γ Δ E mg z ⟩
      z ∈ fromProducts Δ ++ fromProducts E ↔⟨ ++-cong ih₁ ih₂ z ⟩
      z ∈ fromProduct  S ++ fromProduct  T □
  sound Γ       _        (var `&ˡ₁ _)        = ⊥-elim $ noWiths Γ var
  sound Γ       _        (var `&ˡ₂ _)        = ⊥-elim $ noWiths Γ var
  sound Γ       ()       (pr `&ʳ pr₁)

  fromToContext : (xs : List Pr) → xs ≈-bag fromProducts (isProductsToContext xs)
  fromToContext []       = ≈″⇒≈ []
  fromToContext (x ∷ xs) = λ z →
    z ∈ x ∷ xs
               ↔⟨ (refl ∷-cong fromToContext xs) z ⟩
    z ∈ x ∷ fromProducts (isProductsToContext xs)
               ↔⟨ ++-comm (x ∷ []) (fromProducts $ isProductsToContext xs) z ⟩
    z ∈ fromProducts (isProductsToContext $ x ∷ xs) □

  fromToGoal : (x : Pr) (xs : List Pr) → fromProduct (isProductToGoal x xs) ≈-bag x ∷ xs
  fromToGoal x []       = ≈″⇒≈ (x ∷ [])
  fromToGoal x (y ∷ ys) = λ z →
    z ∈ fromProduct (isProductToGoal x ys) ++ y ∷ []
              ↔⟨ ++-comm (fromProduct $ isProductToGoal x ys) (y ∷ []) z ⟩
    z ∈ y ∷ fromProduct (isProductToGoal x ys)
              ↔⟨ (refl ∷-cong fromToGoal x ys) z ⟩
    z ∈ y ∷ x ∷ ys
              ↔⟨ swap-first-two z ⟩
    z ∈ x ∷ y ∷ ys □

  open import lps.ProofSearch
  open Prove Pr _≟_
  open Maybe

  proveM : (xs ys : List Pr) → Maybe $ xs ≈-bag ys
  proveM [] []       = some $ ≈″⇒≈ []
  proveM xs (y ∷ ys) =
    let okContext = isProductsToContext xs
        okGoal    = isProductToGoal y ys
        result    = search (toContext xs) (toGoal y ys)
        bag-eq    = sound okContext okGoal <$> result
   in (λ eq z →
         z ∈ xs                                    ↔⟨ fromToContext xs z ⟩
         z ∈ fromProducts (isProductsToContext xs) ↔⟨ eq z ⟩
         z ∈ fromProduct (isProductToGoal y ys)    ↔⟨ fromToGoal y ys z ⟩
         z ∈ y ∷ ys □) <$> bag-eq
  proveM _  _        = none

  proveBagEq : (xs ys : List Pr) {_ : maybe (const ⊤) ⊥ $ proveM xs ys} → xs ≈-bag ys
  proveBagEq xs ys {pr} = Maybe.induction P ⊥-elim const (proveM xs ys) pr
    where P = λ a → ∀ (pr : maybe (const ⊤) ⊥ a) → xs ≈-bag ys
