module tt.typ.inv where

open import Data.Nat hiding (_<_)
open import Data.Fin hiding (_<_)
open import Data.Product
open import Function

open import tt.Data.NatOmega
open import tt.raw
open import tt.con
open import tt.env
open import tt.red
open import tt.sem
open import tt.typ
open import Relation.Binary.PropositionalEquality as PEq

module TypingInversion (_↝_ : IRel Type) (Red : Reduction SType _↝_) (TRed : TypeReduction _↝_) where

  open Typing _↝_
  open Reduction Red
  open TypeReduction TRed

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
                Σ[ ℓ ∈ ℕ ] A [ _↝_ ⟩* `set ℓ × Γ ⊢set ↑ ℓ ∋ B
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
                                          × Γ ⊢ proj₁ ST ∋ a
                                          × Γ ⊢ Substitution ⊨ proj₂ ST ⟨ `ann a (proj₁ ST) /0⟩T ∋ b
  Γ⊢A∋a,b-inv (`per a b)   = , done , a , b
  Γ⊢A∋a,b-inv (`red r typ) = map id (map (more r) id) $ Γ⊢A∋a,b-inv typ
    
  Γ⊢fste∈A-inv : {n : ℕ} {Γ : ContextT n} {A : Type n} {e : Infer n} →
                 Γ ⊢ `fst e ∈ A → ∃ λ ST → Γ ⊢ e ∈ uncurry `sig ST
  Γ⊢fste∈A-inv (`fst typ)   = , typ
  Γ⊢fste∈A-inv (`red r typ) = Γ⊢fste∈A-inv typ

  Γ⊢snde∈A-inv : {n : ℕ} {Γ : ContextT n} {A : Type n} {e : Infer n} →
                 Γ ⊢ `snd e ∈ A → ∃ λ AB → Γ ⊢ e ∈ uncurry `sig AB
  Γ⊢snde∈A-inv (`snd typ)   = , typ
  Γ⊢snde∈A-inv (`red r typ) = Γ⊢snde∈A-inv typ

  Γ⊢anntA∈A-inv : {n : ℕ} {Γ : ContextT n} {A B : Type n} {t : Check n} →
                  Γ ⊢ `ann t A ∈ B → Γ ⊢set ω ∋ A × Γ ⊢ A ∋ t
  Γ⊢anntA∈A-inv (`ann A t)   = A , t
  Γ⊢anntA∈A-inv (`red r typ) = Γ⊢anntA∈A-inv typ

  Γ⊢appeu∈T-inv : {n : ℕ} {Γ : ContextT n} {A : Type n} {e : Infer n} {u : Check n} →
                  Γ ⊢ `app e u ∈ A → ∃ λ ST → Γ ⊢ e ∈ uncurry `pi ST × Γ ⊢ proj₁ ST ∋ u
  Γ⊢appeu∈T-inv (`app typ u) = , typ , u
  Γ⊢appeu∈T-inv (`red r typ) = Γ⊢appeu∈T-inv typ

  Γ⊢ind∈-inv : {n : ℕ} {Γ : ContextT n} {A : Type n} {p : Type (suc n)} {z s : Check n} {m : Infer n} →
               Γ ⊢ `ind p z s m ∈ A → Γ ∙⟩ `nat ⊢set ω ∋ p
                                    × Γ ⊢ Substitution ⊨ p ⟨ `ann `zro `nat /0⟩T ∋ z
                                    × Γ ⊢ IH p ∋ s
                                    × Γ ⊢ m ∈ `nat
  Γ⊢ind∈-inv (`ind p z s m) = p , z , s , m
  Γ⊢ind∈-inv (`red r typ)   = Γ⊢ind∈-inv typ

  Γ⊢set∋set-inv : {n : ℕ} {Γ : ContextT n} {ℓ : ℕω} {ℓ′ : ℕ} → Γ ⊢set ℓ ∋ `set ℓ′ → ↑ ℓ′ < ℓ
  Γ⊢set∋set-inv (`set lt) = lt
  
  Γ⊢set∋elt-inv : {n : ℕ} {Γ : ContextT n} {ℓ : ℕω} {e : Infer n} →
                  Γ ⊢set ℓ ∋ `elt e → Σ[ ℓ′ ∈ ℕ ] ℓ ≡ ↑ ℓ′ × Γ ⊢ e ∈ `set ℓ′
  Γ⊢set∋elt-inv (`elt e) = , PEq.refl , e
    
  Γ⊢set∋ΣAB-inv : {n : ℕ} {ℓ : ℕω} {Γ : ContextT n} {A : Type n} {B : Type (suc n)} →
                  Γ ⊢set ℓ ∋ `sig A B → Γ ⊢set ℓ ∋ A × Γ ∙⟩ A ⊢set ℓ ∋ B
  Γ⊢set∋ΣAB-inv (`sig A B) = A , B
  
  Γ⊢set∋ΠAB-inv : {n : ℕ} {ℓ : ℕω} {Γ : ContextT n} {A : Type n} {B : Type (suc n)} →
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
        ((A , B) , eq₁ , red₁₁ , red₁₂) = `pi↝*-inv redf
        ((C , D) , eq₂ , red₂₁ , red₂₂) = `pi↝*-inv redg
        (eqAC , eqBD) = `pi-inj $ PEq.trans (sym eq₁) eq₂
        patt          = λ A B → Substitution ⊨ D ⟨ _ /0⟩T [ _↝_ ⟩* Substitution ⊨ B ⟨ `ann _ A /0⟩T
        coerce        = PEq.subst₂ patt (sym eqAC) (sym eqBD)
        open Semantics Substitution
    in Substitution ⊨ B ⟨ `ann _ A /0⟩T
     , mores (subst↝* _ red₁₂) (β↝* B red₁₁)
     , mores (subst↝* _ red₂₂) (coerce $ β↝* D red₂₁)
    
  Γ⊢e∈-unique (`fst t)       (`fst u)       =

    let (ΣST , redt , redu) = Γ⊢e∈-unique t u
        ((A , B) , eq₁ , red₁₁ , red₁₂) = `sig↝*-inv redt
        ((C , D) , eq₂ , red₂₁ , red₂₂) = `sig↝*-inv redu
        (eqAC , _)                      = `sig-inj $ PEq.trans (sym eq₁) eq₂
    in A , red₁₁ , PEq.subst (_ [ _↝_ ⟩*_) (sym eqAC) red₂₁
    
  Γ⊢e∈-unique (`snd t)       (`snd u)       = 

    let (ΣST , redt , redu) = Γ⊢e∈-unique t u
        ((A , B) , eq₁ , red₁₁ , red₁₂) = `sig↝*-inv redt
        ((C , D) , eq₂ , red₂₁ , red₂₂) = `sig↝*-inv redu
        (_ , eqBD)                      = `sig-inj $ PEq.trans (sym eq₁) eq₂
        coerce                          = PEq.subst (_ [ _↝_ ⟩*_) (sym eqBD)
        open Semantics Substitution
    in Substitution ⊨ B ⟨ `fst _ /0⟩T
       , subst↝* _ red₁₂
       , subst↝* _ (coerce red₂₂)

  Γ⊢e∈-unique (`ind p z s m) (`ind q a t n) = , done , done

  Γ⊢e∈-unique (`red r typA)  typB           =
  
    let (C , rAC , rBC) = Γ⊢e∈-unique typA typB
        (R , rAR , rCR) = confluence (more r done) rAC
    in R , rAR , mores rBC rCR
    
  Γ⊢e∈-unique typA           (`red r typB)  =
  
    let (C , rAC , rBC) = Γ⊢e∈-unique typA typB
        (R , rBR , rCR) = confluence (more r done) rBC
    in R , mores rAC rCR , rBR
