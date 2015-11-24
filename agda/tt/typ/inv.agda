module tt.typ.inv where

open import Data.Nat
open import Data.Product
open import Function

open import tt.raw
open import tt.red
open import tt.typ

module TypingInversion (_↝_ : Red Type) where

  open Typing _↝_

  -- Inversion lemmas

  Γ⊢A∋0-inv : {n : ℕ} {Γ : Context n} {A : Type n} → Γ ⊢ A ∋ `zro → A [ _↝_ ⟩* `nat
  Γ⊢A∋0-inv `zro         = done
  Γ⊢A∋0-inv (`red r typ) = more r $ Γ⊢A∋0-inv typ
  
  Γ⊢A∋Sm-inv : {n : ℕ} {Γ : Context n} {A : Type n} {m : Check n} → Γ ⊢ A ∋ `suc m → A [ _↝_ ⟩* `nat
  Γ⊢A∋Sm-inv (`suc _)     = done
  Γ⊢A∋Sm-inv (`red r typ) = more r $ Γ⊢A∋Sm-inv typ
  
  Γ⊢A∋Sm-inv′ : {n : ℕ} {Γ : Context n} {A : Type n} {m : Check n} → Γ ⊢ A ∋ `suc m → Γ ⊢ `nat ∋ m
  Γ⊢A∋Sm-inv′ (`suc m)     = m
  Γ⊢A∋Sm-inv′ (`red r typ) = Γ⊢A∋Sm-inv′ typ 

  Γ⊢A∋typ-inv : {n : ℕ} {Γ : Context n} {A B : Type n} → Γ ⊢ A ∋ `typ B → Σ[ ℓ ∈ ℕ ] A [ _↝_ ⟩* `set ℓ
  Γ⊢A∋typ-inv (`typ A)     = , done
  Γ⊢A∋typ-inv (`red r typ) = map id (more r) $ Γ⊢A∋typ-inv typ
  
  Γ⊢A∋emb-inv : {n : ℕ} {Γ : Context n} {A : Type n} {e : Infer n} → Γ ⊢ A ∋ `emb e → ∃ λ B → Γ ⊢ e ∈ B
  Γ⊢A∋emb-inv (`emb e)     = , e
  Γ⊢A∋emb-inv (`red r typ) = Γ⊢A∋emb-inv typ
  
  Γ⊢A∋λb-inv : {n : ℕ} {Γ : Context n} {A : Type n} {b : Check (suc n)} →
               Γ ⊢ A ∋ `lam b → ∃ λ ST → A [ _↝_ ⟩* uncurry `pi ST
  Γ⊢A∋λb-inv (`lam _)     = , done
  Γ⊢A∋λb-inv (`red r typ) = map id (more r) $ Γ⊢A∋λb-inv typ
  
  Γ⊢A∋a,b-inv : {n : ℕ} {Γ : Context n} {A : Type n} {a b : Check n} →
                Γ ⊢ A ∋ `per a b → ∃ λ ST → A [ _↝_ ⟩* uncurry `sig ST
  Γ⊢A∋a,b-inv (`per _ _)   = , done
  Γ⊢A∋a,b-inv (`red r typ) = map id (more r) $ Γ⊢A∋a,b-inv typ
    
  Γ⊢fste∈A-inv : {n : ℕ} {Γ : Context n} {A : Type n} {e : Infer n} → Γ ⊢ `fst e ∈ A → ∃ λ B → Γ ⊢ e ∈ B
  Γ⊢fste∈A-inv (`fst typ)   = , typ
  Γ⊢fste∈A-inv (`red r typ) = Γ⊢fste∈A-inv typ

  Γ⊢snde∈A-inv : {n : ℕ} {Γ : Context n} {A : Type n} {e : Infer n} → Γ ⊢ `snd e ∈ A → ∃ λ B → Γ ⊢ e ∈ B
  Γ⊢snde∈A-inv (`snd typ)   = , typ
  Γ⊢snde∈A-inv (`red r typ) = Γ⊢snde∈A-inv typ

  Γ⊢anntA∈A-inv : {n : ℕ} {Γ : Context n} {A B : Type n} {t : Check n} → Γ ⊢ `ann t A ∈ B → Γ ⊢ A ∋ t
  Γ⊢anntA∈A-inv (`ann typ)   = typ
  Γ⊢anntA∈A-inv (`red r typ) = Γ⊢anntA∈A-inv typ

  Γ⊢appeu∈T-inv : {n : ℕ} {Γ : Context n} {A : Type n} {e : Infer n} {u : Check n} →
                  Γ ⊢ `app e u ∈ A → ∃ λ B → Γ ⊢ e ∈ B
  Γ⊢appeu∈T-inv (`app typ u) = , typ
  Γ⊢appeu∈T-inv (`red r typ) = Γ⊢appeu∈T-inv typ

{-
  Γ⊢appeu∈T-inv′ : {n : ℕ} {Γ : Context n} {A B : Type n} {e : Infer n} {u : Check n} →
                   Γ ⊢ `app e u ∈ B → Γ ⊢ e ∈ A → ∃ λ ST → A [ _↝_ ⟩* uncurry `pi ST
  Γ⊢appeu∈T-inv′ (`app typ _) _ = , {!done!}
  Γ⊢appeu∈T-inv′ (`red r typ) _ = {!!}
  -}
  
  Γ⊢set∋set-inv : {n : ℕ} {Γ : Context n} {ℓ ℓ′ : ℕ} → Γ ⊢set ℓ ∋ `set ℓ′ → ℓ′ < ℓ
  Γ⊢set∋set-inv (`set lt) = lt
  
  Γ⊢set∋elt-inv : {n : ℕ} {Γ : Context n} {ℓ : ℕ} {e : Infer n} → Γ ⊢set ℓ ∋ `elt e → ∃ λ A → Γ ⊢ e ∈ A
  Γ⊢set∋elt-inv (`elt e) = , e
  
  Γ⊢set∋ΣAB-inv : {n ℓ : ℕ} {Γ : Context n} {A : Type n} {B : Type (suc n)} →
                  Γ ⊢set ℓ ∋ `sig A B → Γ ⊢set ℓ ∋ A × Γ ∙⟩ A ⊢set ℓ ∋ B
  Γ⊢set∋ΣAB-inv (`sig A B) = A , B
  
  Γ⊢set∋ΠAB-inv : {n ℓ : ℕ} {Γ : Context n} {A : Type n} {B : Type (suc n)} →
                  Γ ⊢set ℓ ∋ `pi A B → Γ ⊢set ℓ ∋ A × Γ ∙⟩ A ⊢set ℓ ∋ B
  Γ⊢set∋ΠAB-inv (`pi A B) = A , B
