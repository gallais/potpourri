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

  data isAtom : (σ : ty) → Set where
    `κ : (p : Pr) → isAtom $ `κ p

  data isProduct : (σ : ty) → Set where
    `κ   : (p : Pr) → isProduct $ `κ p
    _`⊗_ : {σ τ : ty} (S : isProduct σ) (T : isProduct τ) → isProduct $ σ `⊗ τ

  isProductToGoal : (x : Pr) (xs : List Pr) → isProduct $ toGoal x xs
  isProductToGoal x []       = `κ x
  isProductToGoal x (y ∷ xs) = isProductToGoal x xs `⊗ `κ y

  fromProduct : {σ : ty} (S : isProduct σ) → List Pr
  fromProduct (`κ p)   = p ∷ []
  fromProduct (S `⊗ T) = fromProduct S ++ fromProduct T

  isAtoms : (Γ : Con ty) → Set
  isAtoms = PCon isAtom

  isAtomsToContext : (xs : List Pr) → isAtoms $ toContext xs
  isAtomsToContext []       = ε
  isAtomsToContext (x ∷ xs) = isAtomsToContext xs ∙ `κ x

  fromAtoms : {γ : Con ty} (Γ : isAtoms γ) → List Pr
  fromAtoms ε          = []
  fromAtoms (Γ ∙ `κ p) = p ∷ fromAtoms Γ 

  noWith : {γ : Con ty} {σ τ : ty} (Γ : isAtoms γ) (var : σ `& τ BT.∈ γ) → ⊥ {lzero}
  noWith (Γ ∙ ()) BT.zro
  noWith (Γ ∙ _)  (BT.suc var) = noWith Γ var

  noTensor : {γ : Con ty} {σ τ : ty} (Γ : isAtoms γ) (var : σ `⊗ τ BT.∈ γ) → ⊥ {lzero}
  noTensor (Γ ∙ ()) BT.zro
  noTensor (Γ ∙ _) (BT.suc var) = noTensor Γ var

  isProducts-merge⁻¹ : {γ δ e : Con ty} (Γ : isAtoms γ) (mg : γ Interleaving.≡ δ ⋈ e) →
                       isAtoms δ × isAtoms e
  isProducts-merge⁻¹ ε       Il.ε         = ε , ε
  isProducts-merge⁻¹ (Γ ∙ S) (mg Il.∙ʳ σ) = Σ-map id (λ E → E ∙ S) $ isProducts-merge⁻¹ Γ mg
  isProducts-merge⁻¹ (Γ ∙ S) (mg Il.∙ˡ σ) = Σ-map (λ Δ → Δ ∙ S) id $ isProducts-merge⁻¹ Γ mg

  import Function-universe as FU
  module FUJ = FU equality-with-J
  open FUJ

  ↔-refl : {xs : List Pr} → xs ≈-bag xs
  ↔-refl {[]}     = ≈″⇒≈ []
  ↔-refl {x ∷ xs} = refl ∷-cong ↔-refl

  isProduct↔ : {σ : ty} (S T : isProduct σ) → fromProduct S ≈-bag fromProduct T
  isProduct↔ (`κ p)     (`κ .p)    = ≈″⇒≈ (p ∷ [])
  isProduct↔ (S₁ `⊗ T₁) (S₂ `⊗ T₂) = ++-cong (isProduct↔ S₁ S₂) (isProduct↔ T₁ T₂)

  isAtoms↔ : {γ : Con ty} (Γ Δ : isAtoms γ) → fromAtoms Γ ≈-bag fromAtoms Δ
  isAtoms↔ ε          ε           = ≈″⇒≈ []
  isAtoms↔ (Γ ∙ `κ p) (Δ ∙ `κ .p) = refl ∷-cong isAtoms↔ Γ Δ

  ++-assoc : (xs ys zs : List Pr) → xs ++ ys ++ zs ≈-bag (xs ++ ys) ++ zs
  ++-assoc []       ys zs = ↔-refl
  ++-assoc (x ∷ xs) ys zs = refl ∷-cong ++-assoc xs ys zs

  isAtoms⋈↔ : {γ δ e : Con ty} (Γ : isAtoms γ) (Δ : isAtoms δ) (E : isAtoms e)
              (mg : γ Interleaving.≡ δ ⋈ e) → fromAtoms Γ ≈-bag fromAtoms Δ ++ fromAtoms E
  isAtoms⋈↔ ε ε ε Il.ε = ≈″⇒≈ []
  isAtoms⋈↔ (Γ ∙ `κ p) Δ (E ∙ `κ .p) (mg Il.∙ʳ .(`κ p)) = λ z →
    z ∈ fromAtoms (Γ ∙ `κ p)                   ↔⟨ (refl ∷-cong isAtoms⋈↔ Γ Δ E mg) z ⟩
    z ∈ p ∷ fromAtoms Δ ++ fromAtoms E         ↔⟨ ++-assoc (p ∷ []) (fromAtoms Δ) (fromAtoms E) z ⟩
    z ∈ (p ∷ [] ++ fromAtoms Δ) ++ fromAtoms E ↔⟨ ++-cong (++-comm (p ∷ []) (fromAtoms Δ)) ↔-refl z ⟩
    z ∈ (fromAtoms Δ ++ p ∷ []) ++ fromAtoms E ↔⟨ inverse (++-assoc (fromAtoms Δ) (p ∷ []) (fromAtoms E) z) ⟩
    z ∈ fromAtoms Δ ++ p ∷ fromAtoms E □
  isAtoms⋈↔ (Γ ∙ `κ p) (Δ ∙ `κ .p) E (mg Il.∙ˡ .(`κ p)) = refl ∷-cong isAtoms⋈↔ Γ Δ E mg

  sound : {γ : Con ty} {σ : ty} (Γ : isAtoms γ) (S : isProduct σ) →
          γ ⊢ σ → fromAtoms Γ ≈-bag fromProduct S
  sound (ε ∙ `κ p) (`κ .p) `v                = ≈″⇒≈ (p ∷ [])
  sound Γ       (S `⊗ T) (tm₁ `⊗ʳ tm₂ by mg) =
    let (Δ , E) = isProducts-merge⁻¹ Γ mg
        ih₁     = sound Δ S tm₁
        ih₂     = sound E T tm₂
    in λ z →
      z ∈ fromAtoms Γ                   ↔⟨ isAtoms⋈↔ Γ Δ E mg z ⟩
      z ∈ fromAtoms Δ ++ fromAtoms E ↔⟨ ++-cong ih₁ ih₂ z ⟩
      z ∈ fromProduct  S ++ fromProduct  T □
  sound Γ       S        (var `⊗ˡ tm)        = ⊥-elim $ noTensor Γ var
  sound Γ       _        (var `&ˡ₁ _)        = ⊥-elim $ noWith   Γ var
  sound Γ       _        (var `&ˡ₂ _)        = ⊥-elim $ noWith   Γ var

  fromToContext : (xs : List Pr) → xs ≈-bag fromAtoms (isAtomsToContext xs)
  fromToContext []       = ≈″⇒≈ []
  fromToContext (x ∷ xs) = refl ∷-cong fromToContext xs

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
    let okContext = isAtomsToContext xs
        okGoal    = isProductToGoal y ys
        result    = search (toContext xs) (toGoal y ys)
        bag-eq    = sound okContext okGoal <$> result
   in (λ eq z →
         z ∈ xs                                    ↔⟨ fromToContext xs z ⟩
         z ∈ fromAtoms (isAtomsToContext xs) ↔⟨ eq z ⟩
         z ∈ fromProduct (isProductToGoal y ys)    ↔⟨ fromToGoal y ys z ⟩
         z ∈ y ∷ ys □) <$> bag-eq
  proveM _  _        = none

  proveBagEq : (xs ys : List Pr) {_ : maybe (const ⊤) ⊥ $ proveM xs ys} → xs ≈-bag ys
  proveBagEq xs ys {pr} = Maybe.induction P ⊥-elim const (proveM xs ys) pr
    where P = λ a → ∀ (pr : maybe (const ⊤) ⊥ a) → xs ≈-bag ys


module Examples where

  open import Data.Nat as Nat
  open Tactics Nat.ℕ Nat._≟_

  1∷2∷3∷3 : 1 ∷ 2 ∷ 3 ∷ 3 ∷ [] ≈-bag 3 ∷ 2 ∷ 3 ∷ 1 ∷ []
  1∷2∷3∷3 = proveBagEq _ _