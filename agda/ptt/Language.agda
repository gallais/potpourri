module ptt.Language where

open import Data.Nat
open import ptt.Context as C hiding (Context)

infixr 5 _`+_ _`⊗_
data Type : Set where
  -- base types
  `𝔹 `ℕ `ℝ `0 `1 : Type
  -- sum type
  _`+_ : (A B : Type) → Type
  -- tensor type
  _`⊗_ : (A B : Type) → Type

Context = C.Context Type

-- Terms
infix 1 _⊢_
infixr 5 _⊨`let_`in_
infix 10 _⊨`⟨_,_⟩


mutual

  data _⊢_ (θ : Context) : (A : Type) → Set where

  -- VARIABLE
    var :
  
      {A : Type} → A ∈ θ →
      --------------------- (var)
              θ ⊢ A

  -- ZERO

    `¡ :
     {A : Type} → θ ⊢ `0 → 
     ----------------------- (magic)
              θ ⊢ A

  -- UNIT
    `*  :
      ----------- (unit)
         θ ⊢ `1

  -- TENSOR
    _⊨`⟨_,_⟩ :
  
      {A B : Type} {Γ Δ : Context} →
      Γ ⋈ Δ ≡ θ → Γ ⊢ A → Δ ⊢ B →
      ------------------------- (⊗)
               θ ⊢ A `⊗ B

    _⊨`let_`in_ :
  
      {A B C : Type} {Γ Δ : Context} →
      Γ ⋈ Δ ≡ θ → Γ ⊢ A `⊗ B → Δ ∙ A ∙ B ⊢ C →
      ----------------------------------------- (let)
                      θ ⊢ C
            
  -- SUM
    `inl :
      {A B : Type} → θ ⊢ A →
      --------------------- (inl)
          θ ⊢ A `+ B
       
    `inr :
      {A B : Type} → θ ⊢ B →
      --------------------- (inr)
           θ ⊢ A `+ B

    _⊨`case_of_%%_ :
      {A B C : Type} {Γ Δ : Context} →
      Γ ⋈ Δ ≡ θ → Γ ⊢ A `+ B → Δ ∙ A ⊢ C → Δ ∙ B ⊢ C →
      ------------------------------------------------- (case)
                            θ ⊢ C

  -- RATIO

    `1/_ :
          (n : ℕ) →
       --------------- (1/2+n)
         θ ⊢ `1 `+ `1
     


swap⊗ : [ `ℕ `⊗ `ℝ ] ⊢ `ℝ `⊗ `ℕ
swap⊗ =
  ⋈ε               ⊨`let var z `in
  [ `ℝ ] ₁⋈₂ [ `ℕ ] ⊨`⟨ var z , var z ⟩


swap+ : [ `ℕ `+ `ℝ ] ⊢ `ℝ `+ `ℕ
swap+ =
  ⋈ε ⊨`case var z
      of `inr (var z)
      %% `inl (var z)

{-


data Term (n : ℕ) : Set where
  `var        : Fin n → Term n
  `*          : Term n
  `⟨_,_⟩      : (t u : Term n) → Term n
  `letin      : (x⊗y : Term n) (t : Term (2 + n)) → Term n
  `¡          : (t : Term n) → Term n
  `inl        : (t : Term n) → Term n
  `inr        : (u : Term n) → Term n
  `case_of_%_ : (t : Term n) (l r : Term (suc n)) → Term n
  `«_,_»      : (t u : Term n) → Term n
  `left       : (t : Term n) → Term n
  `instr[_]_  : (t : Term (suc n)) (u : Term n) → Term n
  `1/_        : ℕ → Term n
  `nrm        : (t : Term n) → Term n
  _`⊕_        : (t u : Term n) → Term n

Context = Vec Type

data _∋_∶_ {n : ℕ} (Γ : Context n) : (k : Fin n) (A : Type) → Set where
   here : ? → ?

data _⊢_∶_ {n : ℕ} (Γ : Context n) : (t : Term n) (A : Type) → Set where
  
-}
