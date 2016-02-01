module tt.typ where

open import Data.Nat hiding (_<_)
open import Data.Fin hiding (_<_)
open import Function

open import tt.Data.NatOmega
open import tt.raw
open import tt.con
open import tt.env
open import tt.sem
open import tt.red


infixr 5 _`→_
_`→_ : {n : ℕ} (a b : Type n) → Type n
a `→ b = `pi a $ weakT extend b

ContextT = Context Type

infix 3 _⊢var_∈_
  
data _⊢var_∈_ : {n : ℕ} → ContextT n → Fin n → Type n → Set where

  zro  : {n : ℕ} {Γ : ContextT n} {A : Type n} →

         ---------------------------------
         Γ ∙⟩ A ⊢var zero ∈ weakT extend A


  suc  : {n : ℕ} {Γ : ContextT n} {A B : Type n} {k : Fin n} →

         Γ ⊢var k ∈ B →
         ----------------------------------
         Γ ∙⟩ A ⊢var suc k ∈ weakT extend B

module Typing (_↝_ : IRel Type) (_≅_ : IRel Type) where

  infix 3 _⊢_∋_ _⊢_∈_ _⊢set_∋_
  
           
  mutual

    data _⊢set_∋_ {n : ℕ} (Γ : ContextT n) : ℕω → Type n → Set where
      
      `sig : {s : Type n} {t : Type (suc n)} {ℓ : ℕω} →
  
             Γ ⊢set ℓ ∋ s → Γ ∙⟩ s ⊢set ℓ ∋ t →
             --------------------------------------
             Γ ⊢set ℓ ∋ `sig s t

      `pi  : {s : Type n} {t : Type (suc n)} {ℓ : ℕω} →
   
             Γ ⊢set ℓ ∋ s → Γ ∙⟩ s ⊢set ℓ ∋ t →
             --------------------------------------
             Γ ⊢set ℓ ∋ `pi s t

      `nat : {ℓ : ℕ} → Γ ⊢set ↑ ℓ ∋ `nat

      `set : {ℓ : ℕω} {ℓ′ : ℕ} →

             ↑ ℓ′ < ℓ →
             --------------------
             Γ ⊢set ℓ ∋ `set ℓ′

      `elt : {ℓ : ℕ} {e : Infer n} →

             Γ ⊢ e ∈ `set ℓ →
             --------------------
             Γ ⊢set ↑ ℓ ∋ `elt e

    data _⊢_∋_ {n : ℕ} (Γ : ContextT n) : Type n → Check n → Set where

      `lam : {b : Check (suc n)} {A : Type n} {B : Type (suc n)} →
    
             Γ ∙⟩ A ⊢ B ∋ b →
             --------------------
             Γ ⊢ `pi A B ∋ `lam b


      `per : {a b : Check n} {A : Type n} {B : Type (suc n)} →

             Γ ⊢ A ∋ a → Γ ⊢ Substitution ⊨ B ⟨ `ann a A /0⟩T ∋ b →
             -----------------------
             Γ ⊢ `sig A B ∋ `per a b

      `zro : Γ ⊢ `nat ∋ `zro

      `suc : {m : Check n} →

             Γ ⊢ `nat ∋ m →
             -----------------
             Γ ⊢ `nat ∋ `suc m

      `emb : {e : Infer n} {A B : Type n} →

             Γ ⊢ e ∈ A → A ≅ B →
             ---------------------
             Γ ⊢ B ∋ `emb e

      `typ : {A : Type n} {ℓ : ℕ} →

             Γ ⊢set ↑ ℓ ∋ A →
             ---------------
             Γ ⊢ `set ℓ ∋ `typ A

      `red : {t : Check n} {A B : Type n} →

             A ↝ B → Γ ⊢ B ∋ t →
             ---------------------
             Γ ⊢ A ∋ t
         

    data _⊢_∈_ {n : ℕ} (Γ : ContextT n) : Infer n → Type n → Set where
  
      `var : {k : Fin n} {A : Type n} →

             Γ ⊢var k ∈ A →
             --------------
             Γ ⊢ `var k ∈ A

      `ann : {t : Check n} {A : Type n} →

             Γ ⊢set ω ∋ A → Γ ⊢ A ∋ t →
             ----------------
             Γ ⊢ `ann t A ∈ A

      `app : {t : Infer n} {u : Check n} {A : Type n} {B : Type (suc n)} →

             Γ ⊢ t ∈ `pi A B → Γ ⊢ A ∋ u →
             -----------------------------
             Γ ⊢ `app t u ∈ Substitution ⊨ B ⟨ `ann u A /0⟩T

      `fst : {t : Infer n} {A : Type n} {B : Type (suc n)} →

             Γ ⊢  t ∈ `sig A B →
             -------------------
             Γ ⊢ `fst t ∈ A

      `snd : {t : Infer n} {A : Type n} {B : Type (suc n)} →

             Γ ⊢  t ∈ `sig A B →
             -------------------
             Γ ⊢ `snd t ∈ Substitution ⊨ B ⟨ `fst t /0⟩T

      `ind : {p : Type (suc n)} {z s : Check n} {m : Infer n} →

             Γ ∙⟩ `nat ⊢set ω ∋ p →
             Γ ⊢ Substitution ⊨ p ⟨ `ann `zro `nat /0⟩T ∋ z →
             Γ ⊢ IH p ∋ s →
             Γ ⊢ m ∈ `nat →
             ---------------------------
             Γ ⊢ `ind p z s m ∈ Substitution ⊨ p ⟨ m /0⟩T

      `red : {e : Infer n} {A B : Type n} →
             A ↝ B → Γ ⊢ e ∈ A →
             -------------------
             Γ ⊢ e ∈ B

    IH : {m : ℕ} (P : Type (suc m)) → Type m
    IH P = `pi `nat ((Substitution ⊨ weakT extend P ⟨ `ann var₀ `nat /0⟩T)
                  `→ (Substitution ⊨ weakT extend P ⟨ `ann (`suc var₀) `nat /0⟩T))

  -- Coercions
  
  reduceInfer : {n : ℕ} {A B : Type n} (red : A [ _↝_ ⟩* B) {Γ : ContextT n} {e : Infer n} →
                Γ ⊢ e ∈ A → Γ ⊢ e ∈ B
  reduceInfer done         typ = typ
  reduceInfer (more r red) typ = reduceInfer red (`red r typ)

  expandCheck : {n : ℕ} {A B : Type n} (red : B [ _↝_ ⟩* A) {Γ : ContextT n} {a : Check n} →
                Γ ⊢ A ∋ a → Γ ⊢ B ∋ a
  expandCheck done         typ = typ
  expandCheck (more r red) typ = `red r (expandCheck red typ)
