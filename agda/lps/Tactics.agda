module lps.Tactics where

open import Bag-equivalence
open import Equality.Propositional

import Relation.Nullary as RN
import Relation.Binary.PropositionalEquality as RBEq
open import lib.Maybe

open import lib.Context
open Context
module BT = BelongsTo
module Il = Interleaving

module MyFin where

  open import Data.Nat hiding (_≟_)
  open import Data.Fin as Fin
  open import lib.Nullary
  open import Function

  suc-inj : {n : ℕ} {k l : Fin n} (eq : Fin.suc k RBEq.≡ suc l) → k RBEq.≡ l
  suc-inj RBEq.refl = RBEq.refl

  _≟_ : {n : ℕ} (k l : Fin n) → RN.Dec (k RBEq.≡ l)
  zero ≟ zero   = RN.yes RBEq.refl
  zero ≟ suc l  = RN.no (λ ())
  suc k ≟ zero  = RN.no (λ ())
  suc k ≟ suc l = dec (k ≟ l) (RN.yes ∘ RBEq.cong suc) (λ p → RN.no $ p ∘ suc-inj)

module TacticsBasics (Pr : Set) where

  open import Prelude
  open import lps.IMLL Pr
  open Type
  open Pointwise

  toContext : List Pr → Con ty
  toContext = foldr (λ p Γ → Γ ∙ `κ p) ε

  toGoal : Pr → List Pr → ty
  toGoal p []       = `κ p
  toGoal p (q ∷ qs) = `κ p `⊗ toGoal q qs

  data isAtom : (σ : ty) → Set where
    `κ : (p : Pr) → isAtom $ `κ p

  data isProduct : (σ : ty) → Set where
    `κ   : (p : Pr) → isProduct $ `κ p
    _`⊗_ : {σ τ : ty} (S : isProduct σ) (T : isProduct τ) → isProduct $ σ `⊗ τ

  isProductToGoal : (x : Pr) (xs : List Pr) → isProduct $ toGoal x xs
  isProductToGoal x []       = `κ x
  isProductToGoal x (y ∷ xs) = `κ x `⊗ isProductToGoal y xs

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

  isAtoms-merge⁻¹ : {γ δ e : Con ty} (Γ : isAtoms γ) (mg : γ Interleaving.≡ δ ⋈ e) →
                       isAtoms δ × isAtoms e
  isAtoms-merge⁻¹ ε       Il.ε         = ε , ε
  isAtoms-merge⁻¹ (Γ ∙ S) (mg Il.∙ʳ σ) = Σ-map id (λ E → E ∙ S) $ isAtoms-merge⁻¹ Γ mg
  isAtoms-merge⁻¹ (Γ ∙ S) (mg Il.∙ˡ σ) = Σ-map (λ Δ → Δ ∙ S) id $ isAtoms-merge⁻¹ Γ mg

  fromToContext : (xs : List Pr) → xs RBEq.≡ fromAtoms (isAtomsToContext xs)
  fromToContext []       = RBEq.refl
  fromToContext (x ∷ xs) = RBEq.cong₂ _∷_ RBEq.refl $ fromToContext xs

  fromToGoal : (x : Pr) (xs : List Pr) → x ∷ xs RBEq.≡ fromProduct (isProductToGoal x xs)
  fromToGoal x []       = RBEq.refl
  fromToGoal x (y ∷ ys) = RBEq.cong₂ _∷_ RBEq.refl $ fromToGoal y ys

module TacticsBagEq (Pr : Set) (_≟_ : (x y : Pr) → RN.Dec (x RBEq.≡ y)) where

  open import Prelude
  open import lps.IMLL Pr
  open Type
  open Pointwise
  open TacticsBasics Pr

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
    let (Δ , E) = isAtoms-merge⁻¹ Γ mg
        ih₁     = sound Δ S tm₁
        ih₂     = sound E T tm₂
    in λ z →
      z ∈ fromAtoms Γ                   ↔⟨ isAtoms⋈↔ Γ Δ E mg z ⟩
      z ∈ fromAtoms Δ ++ fromAtoms E ↔⟨ ++-cong ih₁ ih₂ z ⟩
      z ∈ fromProduct  S ++ fromProduct  T □
  sound Γ       S        (var `⊗ˡ tm)        = ⊥-elim $ noTensor Γ var
  sound Γ       _        (var `&ˡ₁ _)        = ⊥-elim $ noWith   Γ var
  sound Γ       _        (var `&ˡ₂ _)        = ⊥-elim $ noWith   Γ var

  fromToContext′ : (xs : List Pr) → xs ≈-bag fromAtoms (isAtomsToContext xs)
  fromToContext′ xs rewrite RBEq.sym (fromToContext xs) = ↔-refl

  fromToGoal′ : (x : Pr) (xs : List Pr) → fromProduct (isProductToGoal x xs) ≈-bag x ∷ xs
  fromToGoal′ x xs rewrite RBEq.sym (fromToGoal x xs) = ↔-refl

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
         z ∈ xs                                    ↔⟨ fromToContext′ xs z ⟩
         z ∈ fromAtoms (isAtomsToContext xs) ↔⟨ eq z ⟩
         z ∈ fromProduct (isProductToGoal y ys)    ↔⟨ fromToGoal′ y ys z ⟩
         z ∈ y ∷ ys □) <$> bag-eq
  proveM _  _        = none

  proveBagEq : (xs ys : List Pr) {_ : maybe (const ⊤) ⊥ $ proveM xs ys} → xs ≈-bag ys
  proveBagEq xs ys {pr} = Maybe.induction P ⊥-elim const (proveM xs ys) pr
    where P = λ a → ∀ (pr : maybe (const ⊤) ⊥ a) → xs ≈-bag ys

open import Algebra
open CommutativeMonoid
open import Level

module TacticsAbMon
         (Mon : CommutativeMonoid zero zero)
         (_≟_ : (x y : Carrier Mon) → RN.Dec (x RBEq.≡ y)) where

  open import Algebra.Structures
  module M  = CommutativeMonoid Mon

  import Data.Product as Prod
  open import Data.Nat as Nat hiding (_≟_)
  open import Prelude hiding (ℕ; Fin)
  open import Data.Fin
  open import Data.Vec as Vec

  infixl 6 _`∙_
  data Term (n : ℕ) : Set where
    `v   : (k : Fin n)        → Term n 
    `c   : (el : Carrier Mon) → Term n
    _`∙_ : (t u : Term n)     → Term n

  ⟦_⟧ : {n : ℕ} (t : Term n) (ρ : Vec M.Carrier n) → M.Carrier
  ⟦ `v k   ⟧ ρ = Vec.lookup k ρ
  ⟦ `c el  ⟧ ρ = el
  ⟦ t `∙ u ⟧ ρ = ⟦ t ⟧ ρ M.∙ ⟦ u ⟧ ρ

  _∙∙_ : {n : ℕ} → M.Carrier × List (Fin n) → M.Carrier × List (Fin n) → M.Carrier × List (Fin n)
  (e , ks) ∙∙ (f , ls) = e M.∙ f , ks Prelude.++ ls

  norm : {n : ℕ} (t : Term n) → M.Carrier × List (Fin n)
  norm (`v k)   = M.ε , k ∷ []
  norm (`c el)  = el  , []
  norm (t `∙ u) = norm t ∙∙ norm u

  ⟦_⟧s : {n : ℕ} (ks : List $ Fin n) (ρ : Vec M.Carrier n) → M.Carrier
  ⟦ ks ⟧s ρ = Prelude.foldr M._∙_ M.ε $ Prelude.map (flip Vec.lookup ρ) ks

  open import Relation.Binary.EqReasoning M.setoid

  ⟦_`++_⟧s : {n : ℕ} (ks ls : List $ Fin n) (ρ : Vec M.Carrier n) →
            ⟦ ks Prelude.++ ls ⟧s ρ M.≈ ⟦ ks ⟧s ρ M.∙ ⟦ ls ⟧s ρ
  ⟦ []     `++ ls ⟧s ρ = M.sym $ M.identityˡ _
  ⟦ k ∷ ks `++ ls ⟧s ρ =
    begin
      ⟦ k ∷ ks Prelude.++ ls ⟧s ρ                  ≈⟨ M.∙-cong M.refl $ ⟦ ks `++ ls ⟧s ρ ⟩
      Vec.lookup k ρ M.∙ (⟦ ks ⟧s ρ M.∙ ⟦ ls ⟧s ρ) ≈⟨ M.sym $ M.assoc (Vec.lookup k ρ) (⟦ ks ⟧s ρ) (⟦ ls ⟧s ρ) ⟩
      ⟦ k ∷ ks ⟧s ρ M.∙ ⟦ ls ⟧s ρ
    ∎

  ⟦_⟧′ : {n : ℕ} (t : M.Carrier × List (Fin n)) (ρ : Vec M.Carrier n) → M.Carrier
  ⟦ el , ks ⟧′ ρ = el M.∙ ⟦ ks ⟧s ρ

  flip23 : (e f g h : M.Carrier) → (e M.∙ f) M.∙ (g M.∙ h) M.≈ (e M.∙ g) M.∙ (f M.∙ h)
  flip23 e f g h =
    begin
      (e M.∙ f) M.∙ (g M.∙ h) ≈⟨ M.assoc e f (g M.∙ h) ⟩
      e M.∙ (f M.∙ (g M.∙ h)) ≈⟨ M.∙-cong M.refl (M.sym $ M.assoc f g h) ⟩
      e M.∙ (f M.∙ g M.∙ h)   ≈⟨ M.∙-cong M.refl (M.∙-cong (M.comm f g) M.refl) ⟩
      e M.∙ (g M.∙ f M.∙ h)   ≈⟨ M.∙-cong M.refl (M.assoc g f h) ⟩
      e M.∙ (g M.∙ (f M.∙ h)) ≈⟨ M.sym $ M.assoc e g (f M.∙ h) ⟩
      (e M.∙ g) M.∙ (f M.∙ h)
    ∎

  ∙∙-sound : {n : ℕ} (t u : M.Carrier × List (Fin n)) (ρ : Vec M.Carrier n) →
             ⟦ t ⟧′ ρ M.∙ ⟦ u ⟧′ ρ M.≈ ⟦ t ∙∙ u ⟧′ ρ
  ∙∙-sound (e , ks) (f , ls) ρ =
    let F ks = ⟦ ks ⟧s ρ in
    begin
      (e M.∙ F ks) M.∙ (f M.∙ F ls)        ≈⟨ flip23 e (F ks) f (F ls) ⟩
      (e M.∙ f) M.∙ (F ks M.∙ F ls)        ≈⟨ M.∙-cong M.refl (M.sym $ ⟦ ks `++ ls ⟧s ρ) ⟩
      (e M.∙ f) M.∙ (F $ ks Prelude.++ ls)
    ∎

  norm-sound : {n : ℕ} (t : Term n) (ρ : Vec M.Carrier n) → ⟦ t ⟧ ρ M.≈ ⟦ norm t ⟧′ ρ
  norm-sound (`v k)   ρ =
    begin
      Vec.lookup k ρ                   ≈⟨ M.sym $ Prod.proj₂ M.identity _ ⟩
      Vec.lookup k ρ M.∙ M.ε           ≈⟨ M.sym $ Prod.proj₁ M.identity _ ⟩
      M.ε M.∙ (Vec.lookup k ρ M.∙ M.ε)
    ∎
  norm-sound (`c el)  ρ = M.sym $ Prod.proj₂ M.identity _
  norm-sound (t `∙ u) ρ =
    begin
      ⟦ t ⟧ ρ M.∙ ⟦ u ⟧ ρ             ≈⟨ M.∙-cong (norm-sound t ρ) (norm-sound u ρ) ⟩
      ⟦ norm t ⟧′ ρ M.∙ ⟦ norm u ⟧′ ρ ≈⟨ ∙∙-sound (norm t) (norm u) ρ ⟩
      ⟦ norm t ∙∙ norm u ⟧′ ρ
    ∎

  module FixedVars (n : ℕ) (ρ : Vec M.Carrier n) where

    open import lps.IMLL (Fin n)
    open Type
    open Pointwise
    open TacticsBasics (Fin n)

    sound⋈ : {γ δ e : Con ty} (Γ : isAtoms γ) (Δ : isAtoms δ) (E : isAtoms e)
             (mg : γ Interleaving.≡ δ ⋈ e) → ⟦ fromAtoms Γ ⟧s ρ M.≈ ⟦ fromAtoms Δ ⟧s ρ M.∙ ⟦ fromAtoms E ⟧s ρ
    sound⋈ ε ε ε Il.ε = M.sym $ M.identityˡ M.ε
    sound⋈ (Γ ∙ `κ p) Δ (E ∙ `κ .p) (mg Il.∙ʳ .(`κ p)) =
      begin
        ⟦ p ∷ fromAtoms Γ ⟧s ρ                                         ≈⟨ M.∙-cong M.refl $ sound⋈ Γ Δ E mg ⟩
        Vec.lookup p ρ M.∙ (⟦ fromAtoms Δ ⟧s ρ M.∙ ⟦ fromAtoms E ⟧s ρ) ≈⟨ M.sym $ M.assoc _ _ _ ⟩
        ⟦ p ∷ fromAtoms Δ ⟧s ρ M.∙ ⟦ fromAtoms E ⟧s ρ                  ≈⟨ M.∙-cong (M.comm _ _) M.refl ⟩
        ⟦ fromAtoms Δ ⟧s ρ M.∙ Vec.lookup p ρ M.∙ ⟦ fromAtoms E ⟧s ρ   ≈⟨ M.assoc _ _ _ ⟩
        ⟦ fromAtoms Δ ⟧s ρ M.∙ ⟦ p ∷ fromAtoms E ⟧s ρ
      ∎ 
    sound⋈ (Γ ∙ `κ p) (Δ ∙ `κ .p) E (mg Il.∙ˡ .(`κ p)) =
      begin
        ⟦ p ∷ fromAtoms Γ ⟧s ρ                                         ≈⟨ M.∙-cong M.refl $ sound⋈ Γ Δ E mg ⟩
        Vec.lookup p ρ M.∙ (⟦ fromAtoms Δ ⟧s ρ M.∙ ⟦ fromAtoms E ⟧s ρ) ≈⟨ M.sym $ M.assoc _ _ _ ⟩
        ⟦ p ∷ fromAtoms Δ ⟧s ρ M.∙ ⟦ fromAtoms E ⟧s ρ
      ∎

    sound : {γ : Con ty} {σ : ty} (Γ : isAtoms γ) (S : isProduct σ) →
            γ ⊢ σ → ⟦ fromAtoms Γ ⟧s ρ M.≈  ⟦ fromProduct S ⟧s ρ
    sound (ε ∙ `κ p) (`κ .p) `v = M.refl
    sound Γ (S `⊗ T) (s `⊗ʳ t by mg) =
      let (Δ , E) = isAtoms-merge⁻¹ Γ mg
          ih₁     = sound Δ S s
          ih₂     = sound E T t
      in begin
        ⟦ fromAtoms Γ ⟧s ρ                             ≈⟨ sound⋈ Γ Δ E mg ⟩
        ⟦ fromAtoms Δ ⟧s ρ M.∙ ⟦ fromAtoms E ⟧s ρ      ≈⟨ M.∙-cong ih₁ ih₂ ⟩
        ⟦ fromProduct S ⟧s ρ M.∙  ⟦ fromProduct T ⟧s ρ ≈⟨ M.sym $ ⟦ fromProduct S `++ fromProduct T ⟧s ρ ⟩
        ⟦ fromProduct $ S `⊗ T ⟧s ρ
      ∎
    sound Γ _ (var `⊗ˡ _)  = ⊥-elim $ noTensor Γ var
    sound Γ _ (var `&ˡ₁ _) = ⊥-elim $ noWith   Γ var
    sound Γ _ (var `&ˡ₂ _) = ⊥-elim $ noWith   Γ var

  open import lps.ProofSearch
  open import lib.Nullary as LN
  open Maybe

  eq-const : ∀ {n e f} (eq : e RBEq.≡ f) (ρ : Vec M.Carrier n) → ⟦ e , [] ⟧′ ρ M.≈ ⟦ f , [] ⟧′ ρ
  eq-const RBEq.refl ρ = M.refl

  proveM : {n : ℕ} (t u : Term n) (ρ : Vec M.Carrier n) → Maybe $ ⟦ t ⟧ ρ M.≈ ⟦ u ⟧ ρ
  proveM {n} t u ρ with norm t | norm u | norm-sound t ρ | norm-sound u ρ
  ... | (e , []) | (f , [])     | sndt | sndu = flip (dec (e ≟ f)) (const none) $ λ pr → some $
    begin
      ⟦ t ⟧ ρ       ≈⟨ sndt ⟩
      ⟦ e , [] ⟧′ ρ ≈⟨ eq-const pr ρ ⟩
      ⟦ f , [] ⟧′ ρ ≈⟨ M.sym sndu ⟩
      ⟦ u ⟧ ρ
    ∎
  ... | (e , ks) | (f , l ∷ ls) | sndt | sndu =
    flip (dec (e ≟ f)) (const none) $ λ eq →
    let open FixedVars n ρ
        open TacticsBasics (Fin n)
        open Prove (Fin n) (MyFin._≟_ {n})
        okContext = isAtomsToContext ks
        okGoal    = isProductToGoal l ls
        result    = search (toContext ks) (toGoal l ls)
        mon-eq    = sound okContext okGoal <$> result
        fromTo l  = fromProduct ∘ isProductToGoal l
        rew-eqks  = RBEq.subst (λ e → ⟦ e ⟧s ρ M.≈ _) (RBEq.sym $ fromToContext ks)
        rew-eqls  = RBEq.subst (λ e → ⟦ e ⟧s ρ M.≈ ⟦ l ∷ ls ⟧s ρ) (fromToGoal l ls)
    in (λ pr →
        begin
          ⟦ t ⟧ ρ                  ≈⟨ sndt ⟩
          ⟦ e , ks ⟧′ ρ            ≈⟨ M.∙-cong (RBEq.subst (M._≈_ e) eq M.refl) (rew-eqks pr) ⟩
          f M.∙ ⟦ fromTo l ls ⟧s ρ ≈⟨ M.∙-cong M.refl (rew-eqls M.refl) ⟩
          ⟦ f , l ∷ ls ⟧′ ρ        ≈⟨ M.sym sndu ⟩
          ⟦ u ⟧ ρ
        ∎) <$> mon-eq
  ... | (e , ks) | (f , []) | _ | _ = none

  proveMonEq : {n : ℕ} (t u : Term n) (ρ : Vec M.Carrier n) {_ : maybe (const ⊤) ⊥ $ proveM t u ρ} →
               ⟦ t ⟧ ρ M.≈ ⟦ u ⟧ ρ
  proveMonEq t u ρ {pr} = Maybe.induction P ⊥-elim const (proveM t u ρ) pr
    where P = λ a → ∀ (pr : maybe (const ⊤) ⊥ a) → ⟦ t ⟧ ρ M.≈ ⟦ u ⟧ ρ

module Examples where

  open import Algebra.Structures
  open import Data.Nat as Nat
  open import Data.Nat.Properties
  module AbSR = IsCommutativeSemiring isCommutativeSemiring

  open import Data.Fin as Fin hiding (_+_)
  open import Data.Vec as Vec
  open TacticsBagEq Nat.ℕ Nat._≟_
  open TacticsAbMon (record
                       { Carrier = ℕ
                       ; _≈_ = RBEq._≡_
                       ; _∙_ = _+_
                       ; ε   = 0
                       ; isCommutativeMonoid = AbSR.+-isCommutativeMonoid
                       }) Nat._≟_
  import Prelude

  1∷2∷3∷3 : let open Prelude in
            1 ∷ 2 ∷ 3 ∷ 3 ∷ [] ≈-bag 3 ∷ 2 ∷ 3 ∷ 1 ∷ []
  1∷2∷3∷3 = proveBagEq _ _

  1+2+x+y : (x y : ℕ) → 1 + 2 + x + y RBEq.≡ x + 3 + y
  1+2+x+y x y =
     let `x = `v Fin.zero
         `y = `v (Fin.suc Fin.zero)
     in proveMonEq {2} (`c 1 `∙ `c 2 `∙ `x `∙ `y) (`x `∙ `c 3 `∙ `y) (x Vec.∷ y Vec.∷ Vec.[])