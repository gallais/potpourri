module tt.typ.red where

open import Data.Nat
open import Data.Fin
open import Data.Product
open import Function

open import tt.raw
open import tt.con
open import tt.env
open import tt.sem
open import tt.red
open import tt.typ

open import Relation.Binary.PropositionalEquality as PEq hiding ([_])

module ExpandContextTyping
       (_↝_ : IRel Type)
       (weak↝ : {m n : ℕ} {a b : Type m} (inc : m ⊆ n) → a ↝ b → weakT inc a ↝ weakT inc b) where

  open Typing _↝_

  lemmaVar : {m : ℕ} (Γ Δ : ContextT m) {k : Fin m} {B : Type m} →
             Γ [ _[ _↝_ ⟩*_ ] Δ → Δ ⊢var k ∈ B → ∃ λ A → A [ _↝_ ⟩* B × Γ ⊢var k ∈ A
  lemmaVar (Γ ∙⟩ γ) (Δ ∙⟩ δ) (_ , red) zro     = weakT extend γ , wk[ weakT , weak↝ ⟩* extend red , zro
  lemmaVar (Γ ∙⟩ γ) (Δ ∙⟩ δ) (red , _) (suc k) = map (weakT extend) (map (wk[ weakT , weak↝ ⟩* extend) suc) ih
    where ih = lemmaVar Γ Δ red k


  lemma∈   : {m : ℕ} {Γ Δ : ContextT m} {i : Infer m} {B : Type m} →
             Γ [ _[ _↝_ ⟩*_ ] Δ → Δ ⊢ i ∈ B → Γ ⊢ i ∈ B
  lemma∋   : {m : ℕ} {Γ Δ : ContextT m} {t : Check m} {B : Type m} →
             Γ [ _[ _↝_ ⟩*_ ] Δ → Δ ⊢ B ∋ t → Γ ⊢ B ∋ t
  lemmaSet : {m : ℕ} {Γ Δ : ContextT m} {A : Type m} {ℓ : ℕ} →
             Γ [ _[ _↝_ ⟩*_ ] Δ → Δ ⊢set ℓ ∋ A → Γ ⊢set ℓ ∋ A


  lemma∈ redΓΔ (`var k)       = let (_ , red , typ) = lemmaVar _ _ redΓΔ k
                                in reduceInfer red (`var typ)
  lemma∈ redΓΔ (`ann A t)     = `ann (lemmaSet redΓΔ A) $ lemma∋ redΓΔ t
  lemma∈ redΓΔ (`app f t)     = `app (lemma∈ redΓΔ f)   $ lemma∋ redΓΔ t
  lemma∈ redΓΔ (`fst t)       = `fst $ lemma∈ redΓΔ t
  lemma∈ redΓΔ (`snd t)       = `snd $ lemma∈ redΓΔ t
  lemma∈ redΓΔ (`ind p z s m) = `ind (lemmaSet (redΓΔ , done) p) (lemma∋ redΓΔ z) (lemma∋ redΓΔ s) (lemma∈ redΓΔ m)
  lemma∈ redΓΔ (`red r t)     = `red r $ lemma∈ redΓΔ t

  lemma∋ redΓΔ (`lam t)   = `lam $ lemma∋ (redΓΔ , done) t
  lemma∋ redΓΔ (`per a b) = `per (lemma∋ redΓΔ a) (lemma∋ redΓΔ b)
  lemma∋ redΓΔ `zro       = `zro
  lemma∋ redΓΔ (`suc m)   = `suc $ lemma∋ redΓΔ m
  lemma∋ redΓΔ (`emb i)   = `emb $ lemma∈ redΓΔ i
  lemma∋ redΓΔ (`typ A)   = `typ $ lemmaSet redΓΔ A
  lemma∋ redΓΔ (`red r t) = `red r $ lemma∋ redΓΔ t

  lemmaSet redΓΔ (`sig A B) = `sig (lemmaSet redΓΔ A) $ lemmaSet (redΓΔ , done) B
  lemmaSet redΓΔ (`pi A B)  = `pi  (lemmaSet redΓΔ A) $ lemmaSet (redΓΔ , done) B
  lemmaSet redΓΔ `nat       = `nat
  lemmaSet redΓΔ (`set lt)  = `set lt
  lemmaSet redΓΔ (`elt i)   = `elt $ lemma∈ redΓΔ i
  
module ReduceContextTyping
       (_↝_       : IRel Type)
       (red       : Reduction SType _↝_)
       (β↝*       : {m : ℕ} (T : Type (suc m)) {u : Check m} {U U′ : Type m} →
                    U [ _↝_ ⟩* U′ → Substitution ⊨ T ⟨ `ann u U /0⟩T [ _↝_ ⟩* Substitution ⊨ T ⟨ `ann u U′ /0⟩T) 
       (`set↝-inv : {m : ℕ} {ℓ : ℕ} {R : Type m} → `set ℓ [ _↝_ ⟩* R → R ≡ `set ℓ)
       (`nat↝-inv : {m : ℕ} {R : Type m} → `nat [ _↝_ ⟩* R → R ≡ `nat)
       (`pi↝-inv  : {m : ℕ} {A R : Type m} {B : Type (suc m)} →
                    `pi A B [ _↝_ ⟩* R → ∃ λ ST → R ≡ uncurry `pi ST × A [ _↝_ ⟩* proj₁ ST × B [ _↝_ ⟩* proj₂ ST)
       (`sig↝-inv : {m : ℕ} {A R : Type m} {B : Type (suc m)} →
                    `sig A B [ _↝_ ⟩* R → ∃ λ ST → R ≡ uncurry `sig ST × A [ _↝_ ⟩* proj₁ ST × B [ _↝_ ⟩* proj₂ ST)
       where

  open Typing _↝_
  open Reduction red

  lemmaVar : {m : ℕ} (Γ Δ : ContextT m) {k : Fin m} {A : Type m} →
             Γ [ _[ _↝_ ⟩*_ ] Δ → Γ ⊢var k ∈ A → ∃ λ B → A [ _↝_ ⟩* B × Δ ⊢var k ∈ B
  lemmaVar (Γ ∙⟩ γ) (Δ ∙⟩ δ) (_ , red) zro     = weakT extend δ , wk[ weakT , weak↝ ⟩* extend red , zro
  lemmaVar (Γ ∙⟩ γ) (Δ ∙⟩ δ) (red , _) (suc k) = map (weakT extend) (map (wk[ weakT , weak↝ ⟩* extend) suc) ih
    where ih = lemmaVar Γ Δ red k

  lemma∈   : {m : ℕ} {Γ Δ : ContextT m} {i : Infer m} {A : Type m} →
             Γ [ _[ _↝_ ⟩*_ ] Δ → Γ ⊢ i ∈ A → ∃ λ B → A [ _↝_ ⟩* B × Δ ⊢ i ∈ B
  lemma∋   : {m : ℕ} {Γ Δ : ContextT m} {t : Check m} {A B : Type m} →
             Γ [ _[ _↝_ ⟩*_ ] Δ → A [ _↝_ ⟩* B → Γ ⊢ A ∋ t → Δ ⊢ B ∋ t
  lemmaSet : {m : ℕ} {Γ Δ : ContextT m} {A : Type m} {ℓ : ℕ} →
             Γ [ _[ _↝_ ⟩*_ ] Δ → Γ ⊢set ℓ ∋ A → Δ ⊢set ℓ ∋ A


  lemma∈ redΓΔ (`var k)       = map id (map id `var) (lemmaVar _ _ redΓΔ k)
  lemma∈ redΓΔ (`ann A t)     = , done , `ann (lemmaSet redΓΔ A) (lemma∋ redΓΔ done t)
  lemma∈ redΓΔ (`app f t)     =
  
    let (B , red , typ)              = lemma∈ redΓΔ f
        ((S , T) , eq , red₁ , red₂) = `pi↝-inv red
        open Semantics Substitution
    in Substitution ⊨ T ⟨ `ann _ S /0⟩T
     , mores (map[ Type , Type , flip substT (⟦diag⟧ ∙ _) , _↝_ , _↝_ , subst↝ (⟦diag⟧ ∙ _) ⟩* red₂) (β↝* T red₁)
     , `app (PEq.subst (_ ⊢ _ ∈_) eq typ) (lemma∋ redΓΔ red₁ t)

  lemma∈ redΓΔ (`fst t)       =

    let (B , red , typ)              = lemma∈ redΓΔ t
        ((S , T) , eq , red₁ , red₂) = `sig↝-inv red
    in S , red₁ , `fst (PEq.subst (_ ⊢ _ ∈_) eq typ)

  lemma∈ redΓΔ (`snd t)       = 

    let (B , red , typ)              = lemma∈ redΓΔ t
        ((S , T) , eq , red₁ , red₂) = `sig↝-inv red
        open Semantics Substitution
    in Substitution ⊨ T ⟨ `fst _ /0⟩T
     , map[ Type , Type , flip substT (⟦diag⟧ ∙ _) , _↝_ , _↝_ , subst↝ (⟦diag⟧ ∙ _) ⟩* red₂
     , `snd (PEq.subst (_ ⊢ _ ∈_) eq typ)

  lemma∈ redΓΔ (`ind p z s m) =

    let (B , red , typ) = lemma∈ redΓΔ m
    in , done , `ind (lemmaSet (redΓΔ , done) p) (lemma∋ redΓΔ done z) (lemma∋ redΓΔ done s)
                     (PEq.subst (_ ⊢ _ ∈_) (`nat↝-inv red) typ)
    
  lemma∈ redΓΔ (`red r t)     =
  
    let (B , red , typ)   = lemma∈ redΓΔ t
        (R , red₁ , red₂) = confluence (more r done) red
    in , red₁ , reduceInfer red₂ typ
  
  lemma∋ redΓΔ redAB (`lam b)     =

    let ((S , T) , eq , red₁ , red₂) = `pi↝-inv redAB
    in PEq.subst (_ ⊢_∋ _) (sym eq) $ `lam $ lemma∋ (redΓΔ , red₁) red₂ b

  lemma∋ redΓΔ redAB (`per a b)   =

    let ((S , T) , eq , red₁ , red₂) = `sig↝-inv redAB
        open Semantics Substitution
        redb = mores (map[ Type , Type , flip substT (⟦diag⟧ ∙ _) , _↝_ , _↝_ , subst↝ _ ⟩* red₂) (β↝* T red₁)
    in PEq.subst (_ ⊢_∋ _) (sym eq) $ `per (lemma∋ redΓΔ red₁ a) (lemma∋ redΓΔ redb b)
    
  lemma∋ redΓΔ redAB `zro         = PEq.subst (_ ⊢_∋ _) (sym $ `nat↝-inv redAB) `zro
  lemma∋ redΓΔ redAB (`suc m)     = PEq.subst (_ ⊢_∋ _) (sym $ `nat↝-inv redAB) $ `suc $ lemma∋ redΓΔ done m
  lemma∋ redΓΔ redAB (`emb e)     =
  
    let (C , red , typ)   = lemma∈ redΓΔ e
        (R , red₁ , red₂) = confluence redAB red
    in expandCheck red₁ (`emb (reduceInfer red₂ typ))

  lemma∋ redΓΔ redAB (`typ A)     = PEq.subst (_ ⊢_∋ _) (sym $ `set↝-inv redAB) $ `typ (lemmaSet redΓΔ A)
  lemma∋ redΓΔ redAB (`red r typ) =

    let (R , red₁ , red₂) = confluence (more r done) redAB
    in expandCheck red₂ (lemma∋ redΓΔ red₁ typ)
  
  lemmaSet redΓΔ (`sig A B) = `sig (lemmaSet redΓΔ A) $ lemmaSet (redΓΔ , done) B
  lemmaSet redΓΔ (`pi A B)  = `pi  (lemmaSet redΓΔ A) $ lemmaSet (redΓΔ , done) B
  lemmaSet redΓΔ `nat       = `nat
  lemmaSet redΓΔ (`set lt)  = `set lt
  lemmaSet redΓΔ (`elt e)   =

    let (B , red , typ) = lemma∈ redΓΔ e
    in `elt (PEq.subst (_ ⊢ _ ∈_) (`set↝-inv red) typ)
