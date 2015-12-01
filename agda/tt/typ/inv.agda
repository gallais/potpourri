module tt.typ.inv where

open import Data.Nat
open import Data.Fin hiding (_<_)
open import Data.Product
open import Function

open import tt.raw
open import tt.con
open import tt.env
open import tt.red
open import tt.sem
open import tt.typ
open import Relation.Binary.PropositionalEquality as PEq

module TypingInversion (_↝_ : IRel Type) (Red : Reduction SType _↝_)
       (β↝*       : {m : ℕ} (T : Type (suc m)) {u : Check m} {U U′ : Type m} →
                    U [ _↝_ ⟩* U′ → Substitution ⊨ T ⟨ `ann u U /0⟩T [ _↝_ ⟩* Substitution ⊨ T ⟨ `ann u U′ /0⟩T) 
       (`pi↝-inv  : {m : ℕ} {A R : Type m} {B : Type (suc m)} →
                    `pi A B [ _↝_ ⟩* R → ∃ λ ST → R ≡ uncurry `pi ST × A [ _↝_ ⟩* proj₁ ST × B [ _↝_ ⟩* proj₂ ST)
       (`sig↝-inv : {m : ℕ} {A R : Type m} {B : Type (suc m)} →
                    `sig A B [ _↝_ ⟩* R → ∃ λ ST → R ≡ uncurry `sig ST × A [ _↝_ ⟩* proj₁ ST × B [ _↝_ ⟩* proj₂ ST) where

  open Typing _↝_
  open Reduction Red

  -- Inversion lemmas

  Γ⊢A∋0-inv : {n : ℕ} {Γ : ContextT n} {A : Type n} → Γ ⊢ A ∋ `zro → A [ _↝_ ⟩* `nat
  Γ⊢A∋0-inv `zro         = done
  Γ⊢A∋0-inv (`red r typ) = more r $ Γ⊢A∋0-inv typ
  
  Γ⊢A∋Sm-inv : {n : ℕ} {Γ : ContextT n} {A : Type n} {m : Check n} → Γ ⊢ A ∋ `suc m → A [ _↝_ ⟩* `nat
  Γ⊢A∋Sm-inv (`suc _)     = done
  Γ⊢A∋Sm-inv (`red r typ) = more r $ Γ⊢A∋Sm-inv typ
  
  Γ⊢A∋Sm-inv′ : {n : ℕ} {Γ : ContextT n} {A : Type n} {m : Check n} → Γ ⊢ A ∋ `suc m → Γ ⊢ `nat ∋ m
  Γ⊢A∋Sm-inv′ (`suc m)     = m
  Γ⊢A∋Sm-inv′ (`red r typ) = Γ⊢A∋Sm-inv′ typ 

  Γ⊢A∋typ-inv : {n : ℕ} {Γ : ContextT n} {A B : Type n} → Γ ⊢ A ∋ `typ B →
                Σ[ ℓ ∈ ℕ ] A [ _↝_ ⟩* `set ℓ × Γ ⊢set ℓ ∋ B
  Γ⊢A∋typ-inv (`typ A)     = , done , A
  Γ⊢A∋typ-inv (`red r typ) = map id (map (more r) id) $ Γ⊢A∋typ-inv typ
  
  Γ⊢A∋emb-inv : {n : ℕ} {Γ : ContextT n} {A : Type n} {e : Infer n} → Γ ⊢ A ∋ `emb e → ∃ λ B → Γ ⊢ e ∈ B
  Γ⊢A∋emb-inv (`emb e)     = , e
  Γ⊢A∋emb-inv (`red r typ) = Γ⊢A∋emb-inv typ
  
  Γ⊢A∋λb-inv : {n : ℕ} {Γ : ContextT n} {A : Type n} {b : Check (suc n)} →
               Γ ⊢ A ∋ `lam b → ∃ λ ST → A [ _↝_ ⟩* uncurry `pi ST × Γ ∙⟩ proj₁ ST ⊢ proj₂ ST ∋ b
  Γ⊢A∋λb-inv (`lam b)     = , done , b
  Γ⊢A∋λb-inv (`red r typ) = map id (map (more r) id) $ Γ⊢A∋λb-inv typ
  
  Γ⊢A∋a,b-inv : {n : ℕ} {Γ : ContextT n} {A : Type n} {a b : Check n} →
                Γ ⊢ A ∋ `per a b → ∃ λ ST → A [ _↝_ ⟩* uncurry `sig ST
  Γ⊢A∋a,b-inv (`per _ _)   = , done
  Γ⊢A∋a,b-inv (`red r typ) = map id (more r) $ Γ⊢A∋a,b-inv typ
    
  Γ⊢fste∈A-inv : {n : ℕ} {Γ : ContextT n} {A : Type n} {e : Infer n} → Γ ⊢ `fst e ∈ A → ∃ λ B → Γ ⊢ e ∈ B
  Γ⊢fste∈A-inv (`fst typ)   = , typ
  Γ⊢fste∈A-inv (`red r typ) = Γ⊢fste∈A-inv typ

  Γ⊢snde∈A-inv : {n : ℕ} {Γ : ContextT n} {A : Type n} {e : Infer n} → Γ ⊢ `snd e ∈ A → ∃ λ B → Γ ⊢ e ∈ B
  Γ⊢snde∈A-inv (`snd typ)   = , typ
  Γ⊢snde∈A-inv (`red r typ) = Γ⊢snde∈A-inv typ

  Γ⊢anntA∈A-inv : {n : ℕ} {Γ : ContextT n} {A B : Type n} {t : Check n} → Γ ⊢ `ann t A ∈ B → Γ ⊢ A ∋ t
  Γ⊢anntA∈A-inv (`ann _ typ) = typ
  Γ⊢anntA∈A-inv (`red r typ) = Γ⊢anntA∈A-inv typ

  Γ⊢appeu∈T-inv : {n : ℕ} {Γ : ContextT n} {A : Type n} {e : Infer n} {u : Check n} →
                  Γ ⊢ `app e u ∈ A → ∃ λ B → Γ ⊢ e ∈ B
  Γ⊢appeu∈T-inv (`app typ u) = , typ
  Γ⊢appeu∈T-inv (`red r typ) = Γ⊢appeu∈T-inv typ
  
  Γ⊢set∋set-inv : {n : ℕ} {Γ : ContextT n} {ℓ ℓ′ : ℕ} → Γ ⊢set ℓ ∋ `set ℓ′ → ℓ′ < ℓ
  Γ⊢set∋set-inv (`set lt) = lt
  
  Γ⊢set∋elt-inv : {n : ℕ} {Γ : ContextT n} {ℓ : ℕ} {e : Infer n} → Γ ⊢set ℓ ∋ `elt e → Γ ⊢ e ∈ `set ℓ
  Γ⊢set∋elt-inv (`elt e) = e
    
  Γ⊢set∋ΣAB-inv : {n ℓ : ℕ} {Γ : ContextT n} {A : Type n} {B : Type (suc n)} →
                  Γ ⊢set ℓ ∋ `sig A B → Γ ⊢set ℓ ∋ A × Γ ∙⟩ A ⊢set ℓ ∋ B
  Γ⊢set∋ΣAB-inv (`sig A B) = A , B
  
  Γ⊢set∋ΠAB-inv : {n ℓ : ℕ} {Γ : ContextT n} {A : Type n} {B : Type (suc n)} →
                  Γ ⊢set ℓ ∋ `pi A B → Γ ⊢set ℓ ∋ A × Γ ∙⟩ A ⊢set ℓ ∋ B
  Γ⊢set∋ΠAB-inv (`pi A B) = A , B




  Γ⊢var∈-unique : {m : ℕ} {Γ : ContextT m} {k : Fin m} {A B : Type m} →
                  Γ ⊢var k ∈ A → Γ ⊢var k ∈ B → A ≡ B
  Γ⊢e∈-unique : {m : ℕ} {Γ : ContextT m} {e : Infer m} {A B : Type m} →
                Γ ⊢ e ∈ A → Γ ⊢ e ∈ B → ∃ λ C → A [ _↝_ ⟩* C × B [ _↝_ ⟩* C


  Γ⊢var∈-unique zro        zro        = PEq.refl
  Γ⊢var∈-unique (suc typA) (suc typB) = cong (weakT extend) (Γ⊢var∈-unique typA typB)
  
  Γ⊢e∈-unique (`var k)       (`var l) rewrite Γ⊢var∈-unique k l = , done , done
  Γ⊢e∈-unique (`ann t A)     (`ann u B)     = , done , done
  Γ⊢e∈-unique (`app f t)     (`app g u)     =

    let (ΠST , redf , redg)             = Γ⊢e∈-unique f g
        ((A , B) , eq₁ , red₁₁ , red₁₂) = `pi↝-inv redf
        ((C , D) , eq₂ , red₂₁ , red₂₂) = `pi↝-inv redg
        (eqAC , eqBD)                   = `pi-inj $ PEq.trans (sym eq₁) eq₂
        open Semantics Substitution
    in Substitution ⊨ B ⟨ `ann _ A /0⟩T
     , mores (map[ Type , Type , flip substT (⟦diag⟧ ∙ _) , _↝_ , _↝_ , subst↝ (⟦diag⟧ ∙ _) ⟩* red₁₂) (β↝* B red₁₁)
     , mores (map[ Type , Type , flip substT (⟦diag⟧ ∙ _) , _↝_ , _↝_ , subst↝ (⟦diag⟧ ∙ _) ⟩* red₂₂)
             (PEq.subst₂ (λ A B → Substitution ⊨ D ⟨ _ /0⟩T [ _↝_ ⟩* Substitution ⊨ B ⟨ `ann _ A /0⟩T)
                         (sym eqAC) (sym eqBD) (β↝* D red₂₁))
    
  Γ⊢e∈-unique (`fst t)       (`fst u)       =

    let (ΣST , redt , redu) = Γ⊢e∈-unique t u
        ((A , B) , eq₁ , red₁₁ , red₁₂) = `sig↝-inv redt
        ((C , D) , eq₂ , red₂₁ , red₂₂) = `sig↝-inv redu
        (eqAC , _)                      = `sig-inj $ PEq.trans (sym eq₁) eq₂
    in A , red₁₁ , PEq.subst (_ [ _↝_ ⟩*_) (sym eqAC) red₂₁
    
  Γ⊢e∈-unique (`snd t)       (`snd u)       = 

    let (ΣST , redt , redu) = Γ⊢e∈-unique t u
        ((A , B) , eq₁ , red₁₁ , red₁₂) = `sig↝-inv redt
        ((C , D) , eq₂ , red₂₁ , red₂₂) = `sig↝-inv redu
        (_ , eqBD)                      = `sig-inj $ PEq.trans (sym eq₁) eq₂
        open Semantics Substitution
    in Substitution ⊨ B ⟨ `fst _ /0⟩T
       , map[ Type , Type , flip substT (⟦diag⟧ ∙ _) , _↝_ , _↝_ , subst↝ (⟦diag⟧ ∙ _) ⟩* red₁₂
       , map[ Type , Type , flip substT (⟦diag⟧ ∙ _) , _↝_ , _↝_ , subst↝ (⟦diag⟧ ∙ _) ⟩*
           (PEq.subst (_ [ _↝_ ⟩*_) (sym eqBD) red₂₂)

  Γ⊢e∈-unique (`ind p z s m) (`ind q a t n) = , done , done

  Γ⊢e∈-unique (`red r typA)  typB           =
  
    let (C , rAC , rBC) = Γ⊢e∈-unique typA typB
        (R , rAR , rCR) = confluence (more r done) rAC
    in R , rAR , mores rBC rCR
    
  Γ⊢e∈-unique typA           (`red r typB)  =
  
    let (C , rAC , rBC) = Γ⊢e∈-unique typA typB
        (R , rBR , rCR) = confluence (more r done) rBC
    in R , mores rAC rCR , rBR
