import lps.IMLL as IMLL

open import Data.Product hiding (map)
open import Data.Nat
open import Function

import lib.Context as Con
open import lib.Maybe
open import lib.Nullary

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

module lps.Linearity (Pr : Set) where

  module Type where

    open IMLL.Type Pr
    open Con.Context

    -- our definition is a bit convoluted because we want to avoid
    -- having multiple proofs of the same statement.
    -- E.g. [ σ `& τ ] saying that σ `& τ is free
    -- and  S ̀&ˡ τ    saying that we have picked the left hand side
    -- despite the fact that S is a cover with only available atoms
    private
      module DummyCover where
        data Cover : ty → Set where
          `κ     : (k : Pr) → Cover $ `κ k
          _`⊗_   : {a b : ty} (A : Cover a) (B : Cover b) → Cover $ a `⊗ b
          [_]`⊗_ : (a : ty) {b : ty} (B : Cover b) → Cover $ a `⊗ b
          _`⊗[_] : {a : ty} (A : Cover a) (b : ty) → Cover $ a `⊗ b
          -- BOTH sides of an additive conjunction can be used if and only if
          -- they are entirely eaten up. Hence the lack of recursive arg.
          _`&_   : (a b : ty) → Cover $ a `& b
          _`&[_]  : {a : ty} (A : Cover a) (b : ty) → Cover $ a `& b
          [_]`&_  : (a : ty) {b : ty} (B : Cover b) → Cover $ a `& b
      open DummyCover public hiding (module Cover)

    module Cover where

      data isUsed : {σ : ty} (S : Cover σ) → Set where
        `κ     : (k : Pr) → isUsed $ `κ k
        _`⊗_   : {a b : ty} {A : Cover a} {B : Cover b}
                 (prA : isUsed A) (prB : isUsed B) → isUsed $ A `⊗ B
        _`&_   : (a b : ty) → isUsed $ a `& b
        _`&[_] : {a : ty} {A : Cover a} (prA : isUsed A) (b : ty) →
                 isUsed $ A `&[ b ]
        [_]`&_ : (a : ty) {b : ty} {B : Cover b} (prB : isUsed B) →
                 isUsed $ [ a ]`& B


      isUsed&ˡ⁻¹ : {a b : ty} {A : Cover a} → isUsed $ A `&[ b ] → isUsed A
      isUsed&ˡ⁻¹ (pr `&[ _ ]) = pr

      isUsed&ʳ⁻¹ : {a b : ty} {B : Cover b} → isUsed $ [ a ]`& B → isUsed B
      isUsed&ʳ⁻¹ ([ _ ]`& pr) = pr

      isUsed⊗⁻¹₁ : ∀ {a b} {A : Cover a} {B : Cover b} → isUsed $ A `⊗ B → isUsed A 
      isUsed⊗⁻¹₁ (pr `⊗ _) = pr

      isUsed⊗⁻¹₂ : ∀ {a b} {A : Cover a} {B : Cover b} → isUsed $ A `⊗ B → isUsed B
      isUsed⊗⁻¹₂ (_ `⊗ pr) = pr

      isUsed? : ∀ {σ} (S : Cover σ) → Dec $ isUsed S
      isUsed? (`κ k )     = yes $ `κ k
      isUsed? (A `⊗ B)    = ihA
        where
          val : isUsed A → isUsed B → Dec $ isUsed $ A `⊗ B
          val prA prB = yes $ prA `⊗ prB
          ihB : isUsed A → Dec $ isUsed $ A `⊗ B
          ihB prA = dec (isUsed? B) (val prA) (λ ¬p → no $ ¬p ∘ isUsed⊗⁻¹₂)
          ihA     = dec (isUsed? A) ihB (λ ¬p → no $ ¬p ∘ isUsed⊗⁻¹₁)
      isUsed? ([ a ]`⊗ B) = no (λ ())
      isUsed? (A `⊗[ b ]) = no (λ ())
      isUsed? (a `& b)    = yes (a `& b)
      isUsed? (A `&[ b ]) = dec (isUsed? A) (λ prA → yes $ prA `&[ b ])
                                            (λ ¬p  → no $ ¬p ∘ isUsed&ˡ⁻¹)
      isUsed? ([ a ]`& B) = dec (isUsed? B) (λ prB → yes $ [ a ]`& prB)
                                            (λ ¬p  → no $ ¬p ∘ isUsed&ʳ⁻¹)

      ｢_｣ : {σ : ty} (S : Cover σ) → Con ty
      ｢ `κ k      ｣ = ε ∙ `κ k
      ｢ A `⊗ B    ｣ = ｢ A ｣ Context.++ ｢ B ｣
      ｢ [ a ]`⊗ B ｣ = ｢ B ｣
      ｢ A `⊗[ b ] ｣ = ｢ A ｣
      ｢ a `& b    ｣ = ε ∙ a `& b
      ｢ A `&[ b ] ｣ = ｢ A ｣
      ｢ [ a ]`& B ｣ = ｢ B ｣

      open IMLL Pr
      open Con.Context
      open Con.Context.Context
      open Con.BelongsTo
      open BelongsTo

      tm-group⁻¹ : (Γ Δ E F : Con ty) {σ : ty} (tm : Γ ++ (Δ ++ E) ++ F ⊢ σ) →
                   Γ ++ Δ ++ E ++ F ⊢ σ
      tm-group⁻¹ Γ Δ E F {σ} = Eq.subst (λ C → C ++ F ⊢ σ) $ Eq.sym $ assoc++ Γ Δ E

      ⟦isUsed⟧ : (Γ Δ : Con ty) {σ τ : ty} {S : Cover σ} (prS : isUsed S)
                (tm : Γ ++ ｢ S ｣ ++ Δ ⊢ τ) → Γ ∙ σ ++ Δ ⊢ τ
      ⟦isUsed⟧ Γ Δ (`κ k)                tm = tm
      ⟦isUsed⟧ Γ Δ {a `⊗ b} {τ} {A `⊗ B} (prA `⊗ prB) tm = 
        let pr  = ∈++ˡ Δ zro
            rew = assoc++ (Γ ++ ｢ A ｣) (ε ∙ b) Δ
            ih₁ = ⟦isUsed⟧ (Γ ++ ｢ A ｣) Δ prB $ tm-group⁻¹ Γ ｢ A ｣ ｢ B ｣ Δ tm
            ih₂ = ⟦isUsed⟧ Γ (ε ∙ b ++ Δ) prA $ Eq.subst (flip _⊢_ τ) rew ih₁
            rew = Eq.trans (actAt++ˡ Δ zro) $ assoc++ (Γ ∙ a) (ε ∙ b) Δ
        in pr `⊗ˡ Eq.subst (flip _⊢_ τ) (Eq.sym rew) ih₂
      ⟦isUsed⟧ Γ Δ (a `& b)      tm = tm
      ⟦isUsed⟧ Γ Δ (prA `&[ b ]) tm =
        let pr  = ∈++ˡ Δ zro
            rew = Eq.sym $ actAt++ˡ Δ zro
            ih  = ⟦isUsed⟧ Γ Δ prA tm
        in pr `&ˡ₁ Eq.subst (flip _⊢_ _) rew ih
      ⟦isUsed⟧ Γ Δ ([ a ]`& prB) tm = 
        let pr  = ∈++ˡ Δ zro
            rew = Eq.sym $ actAt++ˡ Δ zro
            ih  = ⟦isUsed⟧ Γ Δ prB tm
        in pr `&ˡ₂ Eq.subst (flip _⊢_ _) rew ih

    private
       module DummyUsage where

         data Usage : ty → Set where
           [_] : (a : ty) → Usage a
           ]_[ : {a : ty} (A : Cover a) → Usage a

    open DummyUsage public hiding (module Usage)

    module Usage where

      data isUsed {σ : ty} : (S : Usage σ) → Set where
        ]_[ : {A : Cover σ} (prA : Cover.isUsed A) → isUsed ] A [
      
      isUsed]_[⁻¹ : {σ : ty} {A : Cover σ} (prS : isUsed ] A [) → Cover.isUsed A
      isUsed] ] prA [ [⁻¹ = prA

      isUsed? : {σ : ty} (S : Usage σ) → Dec $ isUsed S
      isUsed? [ σ ] = no (λ ())
      isUsed? ] A [  = dec (Cover.isUsed? A) (yes ∘ ]_[)
                                             (λ ¬p → no $ ¬p ∘ isUsed]_[⁻¹)

      ｢_｣ : {σ : ty} (S : Usage σ) → Con ty
      ｢ [ a ] ｣ = ε
      ｢ ] A [ ｣ = Cover.｢ A ｣

      open IMLL Pr
      open Con.Context.Context

      ⟦isUsed⟧ : (Γ Δ : Con ty) {σ τ : ty} {S : Usage σ} (prS : isUsed S)
                (tm : Γ ++ ｢ S ｣ ++ Δ ⊢ τ) → Γ ∙ σ ++ Δ ⊢ τ
      ⟦isUsed⟧ Γ Δ ] prA [ = Cover.⟦isUsed⟧ Γ Δ prA

  module Context where

    open IMLL.Type Pr
    open Con.Context
    open Con.Context.Pointwise
  
    Usage : Con ty → Set
    Usage = PCon Type.Usage

    inj[_] : (γ : Con ty) → Usage γ
    inj[_] = Pointwise.pointwise Type.[_]

    ｢_｣ : {γ : Con ty} (Γ : Usage γ) → Con ty
    ｢_｣ = Pointwise.induction _ (λ prP ih → ih Context.++ Type.Usage.｢ prP ｣ ) ε

    data isUsed : {γ : Con ty} (Γ : Usage γ) → Set where
      ε   : isUsed ε
      _∙_ : ∀ {γ σ} {Γ : Usage γ} {S : Type.Usage σ} (prΓ : isUsed Γ)
            (prS : Type.Usage.isUsed S) → isUsed $ Γ ∙ S

    isUsed∙⁻¹₁ : {γ : Con ty} {σ : ty} {Γ : Usage γ} {S : Type.Usage σ}
                 (prΓσ : isUsed $ Γ ∙ S) → isUsed Γ
    isUsed∙⁻¹₁ (prΓ ∙ prS) = prΓ

    isUsed∙⁻¹₂ : {γ : Con ty} {σ : ty} {Γ : Usage γ} {S : Type.Usage σ}
                 (prΓσ : isUsed $ Γ ∙ S) → Type.Usage.isUsed S
    isUsed∙⁻¹₂ (prΓ ∙ prS) = prS

    isUsed? : {γ : Con ty} (Γ : Usage γ) → Dec $ isUsed Γ
    isUsed? ε       = yes ε
    isUsed? (Γ ∙ S) =
      flip (dec (Type.Usage.isUsed? S)) (λ ¬p → no $ ¬p ∘ isUsed∙⁻¹₂) $ λ prS →
      dec (isUsed? Γ) (λ prΓ → yes $ prΓ ∙ prS) (λ ¬p → no $ ¬p ∘ isUsed∙⁻¹₁)

    ｢inj[_]｣ : (γ : Con ty) → ｢ inj[ γ ] ｣ ≡ ε
    ｢inj[_]｣ = Context.induction (λ _ → id) Eq.refl

    open IMLL Pr
    open IMLL.RewriteRules Pr
    open Con.Context.Context

    ⟦isUsed⟧ : {γ : Con ty} {τ : ty} {Γ : Usage γ} (prΓ : isUsed Γ)
              (tm : ｢ Γ ｣ ⊢ τ) → γ ⊢ τ
    ⟦isUsed⟧ = helper ε _ _
      where
        helper : (Δ γ : Con ty) {τ : ty} (Γ : Usage γ) (prΓ : isUsed Γ)
                 (tm : ｢ Γ ｣ ++ Δ ⊢ τ) → γ ++ Δ ⊢ τ
        helper Δ ε       ε       ε           tm = tm
        helper Δ (γ ∙ σ) (Γ ∙ S) (prΓ ∙ prS) tm =
          let step = Type.Usage.⟦isUsed⟧ ｢ Γ ｣ Δ prS tm
              ih   = helper (ε ∙ σ ++ Δ) γ Γ prΓ $ tm-assoc ｢ Γ ｣ (ε ∙ σ) Δ step
          in tm-assoc⁻¹ γ (ε ∙ σ) Δ ih

module LT  = Type
module LTC = Type.Cover
module LTU = Type.Usage
module LC  = Context
