module tt.typ where

open import Data.Nat
open import Data.Fin hiding (_<_)
open import Function
open import Relation.Binary.PropositionalEquality as PEq using (_≡_ ; subst)

open import tt.raw
open import tt.env
open import tt.sem
open import tt.sem.fus


infixr 5 _`→_
_`→_ : {n : ℕ} (a b : Type n) → Type n
a `→ b = pi a $ weakT extend b


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
           
record [_]_⇒_ {m n : ℕ} (inc : m ⊆ n) (Γ : Context m) (Δ : Context n) : Set where
  constructor pack
  field weakVar : {k : Fin m} {A : Type m} → Γ ⊢var k ∈ A → Δ ⊢var lookup inc k ∈ weakT inc A
open [_]_⇒_ public

POP! : {m n : ℕ} {inc : m ⊆ n} {Γ : Context m} {Δ : Context n} →
       [ inc ] Γ ⇒ Δ → (A : Type m) → [ pop! inc ] Γ ∙⟩ A ⇒ (Δ ∙⟩ weakT inc A)
weakVar (POP! {inc = inc} {Δ = Δ} ren A) zro =

  let eq : weakT extend (weakT inc A)
         ≡ weakT (pop! inc) (weakT extend A)
      eq = PEq.trans (fusion.lemmaT RenRen A (λ _ → PEq.refl))
         $ PEq.sym $ fusion.lemmaT RenRen A (λ _ → PEq.refl)

  in subst (Δ ∙⟩ weakT inc A ⊢var zero ∈_) eq zro

weakVar (POP! {inc = inc} {Δ = Δ} ren A) (suc {B = B} {k} Hk) =
  
  let ih : Δ ∙⟩ weakT inc A ⊢var lookup (pop! inc) (suc k) ∈ weakT extend (weakT inc B)
      ih = suc (weakVar ren Hk)

      eq : weakT extend (weakT inc B)
         ≡ weakT (pop! inc) (weakT extend B)
      eq = PEq.trans (fusion.lemmaT RenRen B (λ _ → PEq.refl))
         $ PEq.sym $  fusion.lemmaT RenRen B (λ _ → PEq.refl)
        
  in subst (Δ ∙⟩ weakT inc A ⊢var lookup (pop! inc) (suc k) ∈_) eq ih


module Typing (_↝_ : {n : ℕ} (a b : Type n) → Set) where

  infix 1 _⊢_∋_ _⊢_∈_ _⊢set_∋_
  
           
  mutual

    data _⊢set_∋_ {n : ℕ} (Γ : Context n) : ℕ → Type n → Set where
      
      `sig : {s : Type n} {t : Type (suc n)} {ℓ : ℕ} →
  
             Γ ⊢set ℓ ∋ s → Γ ∙⟩ s ⊢set ℓ ∋ t →
             --------------------------------------
             Γ ⊢set ℓ ∋ sig s t

      `pi  : {s : Type n} {t : Type (suc n)} {ℓ : ℕ} →
   
             Γ ⊢set ℓ ∋ s → Γ ∙⟩ s ⊢set ℓ ∋ t →
             --------------------------------------
             Γ ⊢set ℓ ∋ pi s t

      `nat : Γ ⊢set 0 ∋ El `nat

      `set : {ℓ ℓ′ : ℕ} →

             ℓ > ℓ′ →
             --------------------
             Γ ⊢set ℓ ∋ set ℓ′

    data _⊢_∋_ {n : ℕ} (Γ : Context n) : Type n → Check n → Set where

      `lam : {b : Check (suc n)} {A : Type n} {B : Type (suc n)} →
    
             Γ ∙⟩ A ⊢ B ∋ b →
             --------------------
             Γ ⊢ pi A B ∋ `lam b


      `per : {a b : Check n} {A : Type n} {B : Type (suc n)} →

             Γ ⊢ A ∋ a → Γ ⊢ Substitution ⊨ B ⟨ `ann a A /0⟩T ∋ b →
             -----------------------
             Γ ⊢ sig A B ∋ `per a b

      `zro : Γ ⊢ nat ∋ `zro

      `suc : {m : Check n} →

             Γ ⊢ nat ∋ m →
             -----------------
             Γ ⊢ nat ∋ `suc m

      `emb : {e : Infer n} {A : Type n} →

             Γ ⊢ e ∈ A →
             -----------
             Γ ⊢ A ∋ `emb e

      `set : {A : Type n} {ℓ : ℕ} →

             Γ ⊢set ℓ ∋ A →
             ---------------
             Γ ⊢ set ℓ ∋ unEl A

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

             Γ ⊢ t ∈ pi A B → Γ ⊢ A ∋ u →
             -----------------------------
             Γ ⊢ `app t u ∈ Substitution ⊨ B ⟨ `ann u A /0⟩T

      `fst : {t : Infer n} {A : Type n} {B : Type (suc n)} →

             Γ ⊢  t ∈ sig A B →
             -------------------
             Γ ⊢ `fst t ∈ A

      `snd : {t : Infer n} {A : Type n} {B : Type (suc n)} →

             Γ ⊢  t ∈ sig A B →
             -------------------
             Γ ⊢ `snd t ∈ Substitution ⊨ B ⟨ `fst t /0⟩T

      `ind : {p z s : Check n} {m : Infer n} {ℓ : ℕ} →

             let pTy : {n : ℕ} → Type n
                 pTy = λ {n} → pi nat (set ℓ) in

             Γ ⊢ pTy ∋ p →
             Γ ⊢ El (app p pTy `zro) ∋ z →

             let P : {m : ℕ} → n ⊆ m → Check m → Type m
                 P = λ inc x → El (app (weakC inc p) pTy x) in

             Γ ⊢ pi nat (P extend var₀ `→ P extend (`suc var₀)) ∋ s →
             Γ ⊢ m ∈ nat →
             ---------------------------
             Γ ⊢ `ind p z s m ∈ El (app p pTy (`emb m))

      `red : {e : Infer n} {A B : Type n} →
             A ↝ B → Γ ⊢ e ∈ A →
             -------------------
             Γ ⊢ e ∈ B
