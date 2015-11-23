module tt.typ where

open import Data.Nat
open import Data.Fin hiding (_<_)
open import Function
open import Relation.Binary.PropositionalEquality as PEq using (_≡_ ; subst)

open import tt.raw
open import tt.env
open import tt.sem


infixr 5 _`→_
_`→_ : {n : ℕ} (a b : Type n) → Type n
a `→ b = `pi a $ weakT extend b


infixl 5 _∙⟩_
data Context : ℕ → Set where
  ⟨⟩    : Context 0
  _∙⟩_  : {n : ℕ} (Γ : Context n) (A : Type n) → Context (suc n)
  
infix 1 _⊢var_∈_
  
data _⊢var_∈_ : {n : ℕ} → Context n → Fin n → Type n → Set where

  zro  : {n : ℕ} {Γ : Context n} {A : Type n} →

         ---------------------------------
         Γ ∙⟩ A ⊢var zero ∈ weakT extend A


  suc  : {n : ℕ} {Γ : Context n} {A B : Type n} {k : Fin n} →

         Γ ⊢var k ∈ B →
         ----------------------------------
         Γ ∙⟩ A ⊢var suc k ∈ weakT extend B

module Typing (_↝_ : {n : ℕ} (a b : Type n) → Set) where

  infix 1 _⊢_∋_ _⊢_∈_ _⊢set_∋_
  
           
  mutual

    data _⊢set_∋_ {n : ℕ} (Γ : Context n) : ℕ → Type n → Set where
      
      `sig : {s : Type n} {t : Type (suc n)} {ℓ : ℕ} →
  
             Γ ⊢set ℓ ∋ s → Γ ∙⟩ s ⊢set ℓ ∋ t →
             --------------------------------------
             Γ ⊢set ℓ ∋ `sig s t

      `pi  : {s : Type n} {t : Type (suc n)} {ℓ : ℕ} →
   
             Γ ⊢set ℓ ∋ s → Γ ∙⟩ s ⊢set ℓ ∋ t →
             --------------------------------------
             Γ ⊢set ℓ ∋ `pi s t

      `nat : Γ ⊢set 0 ∋ `nat

      `set : {ℓ ℓ′ : ℕ} →

             ℓ > ℓ′ →
             --------------------
             Γ ⊢set ℓ ∋ `set ℓ′

      `elt : {ℓ : ℕ} {e : Infer n} →

             Γ ⊢ e ∈ `set ℓ →
             --------------------
             Γ ⊢set ℓ ∋ `elt e

    data _⊢_∋_ {n : ℕ} (Γ : Context n) : Type n → Check n → Set where

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

      `emb : {e : Infer n} {A : Type n} →

             Γ ⊢ e ∈ A →
             -----------
             Γ ⊢ A ∋ `emb e

      `typ : {A : Type n} {ℓ : ℕ} →

             Γ ⊢set ℓ ∋ A →
             ---------------
             Γ ⊢ `set ℓ ∋ `typ A

      `red : {t : Check n} {A B : Type n} →

             A ↝ B → Γ ⊢ B ∋ t →
             ---------------------
             Γ ⊢ A ∋ t
         

    data _⊢_∈_ {n : ℕ} (Γ : Context n) : Infer n → Type n → Set where
  
      `var : {k : Fin n} {A : Type n} →

             Γ ⊢var k ∈ A →
             --------------
             Γ ⊢ `var k ∈ A

      `ann : {t : Check n} {A : Type n} →

             Γ ⊢ A ∋ t →
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

      `ind : {p z s : Check n} {m : Infer n} {ℓ : ℕ} →

             let pTy : {n : ℕ} → Type n
                 pTy = λ {n} → `pi `nat (`set ℓ) in

             Γ ⊢ pTy ∋ p →
             Γ ⊢ appT p pTy `zro ∋ z →

             let P : {m : ℕ} → n ⊆ m → Check m → Type m
                 P = λ inc x → appT (weakC inc p) pTy x in

             Γ ⊢ `pi `nat (P extend var₀ `→ P extend (`suc var₀)) ∋ s →
             Γ ⊢ m ∈ `nat →
             ---------------------------
             Γ ⊢ `ind p z s m ∈ appT p pTy (`emb m)

      `red : {e : Infer n} {A B : Type n} →
             A ↝ B → Γ ⊢ e ∈ A →
             -------------------
             Γ ⊢ e ∈ B
