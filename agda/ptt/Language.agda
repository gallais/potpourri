module ptt.Language where

open import Data.Nat
open import Data.List hiding (_∷ʳ_)

infixr 5 _`+_ _`⊗_
data Type : Set where
  -- base types
  `𝔹 `ℕ `ℝ `0 `1 : Type
  -- sum type
  _`+_ : (A B : Type) → Type
  -- tensor type
  _`⊗_ : (A B : Type) → Type

Context = List Type

-- Variable in a context
infix 1 _∈_
data _∈_ (A : Type) : (Γ : Context) → Set where
  z : {Γ : Context} → A ∈ A ∷ Γ
  s : {Γ : Context} {B : Type} (m : A ∈ Γ) → A ∈ B ∷ Γ

-- Context interleaving
infix 1 _⋈_≡_
data _⋈_≡_ : (Γ Δ θ : Context) → Set where
  []   : [] ⋈ [] ≡ []
  _∷ˡ_ : (A : Type) {Γ Δ θ : Context} (tl : Γ ⋈ Δ ≡ θ) → A ∷ Γ ⋈ Δ     ≡ A ∷ θ
  _∷ʳ_ : (A : Type) {Γ Δ θ : Context} (tl : Γ ⋈ Δ ≡ θ) → Γ     ⋈ A ∷ Δ ≡ A ∷ θ

induction :
  (P : Context → Set)
  (p[] : P [])
  (p∷  : (A : Type) (Γ : Context) → P Γ → P (A ∷ Γ)) →
  (Γ : Context) → P Γ
induction P p[] p∷ []      = p[]
induction P p[] p∷ (A ∷ Γ) = p∷ A Γ (induction P p[] p∷ Γ)

⋈[] : {Γ : Context} → Γ ⋈ [] ≡ Γ
⋈[] {Γ} = induction (λ Γ → Γ ⋈ [] ≡ Γ) [] (λ A _ ih → A ∷ˡ ih) Γ

[]⋈ : {Γ : Context} → [] ⋈ Γ ≡ Γ
[]⋈ {Γ} = induction (λ Γ → [] ⋈ Γ ≡ Γ) [] (λ A _ ih → A ∷ʳ ih) Γ

_₁⋈₂_ : (Γ Δ : Context) → Γ ⋈ Δ ≡ Γ ++ Δ
Γ ₁⋈₂ Δ = induction (λ Γ → Γ ⋈ Δ ≡ Γ ++ Δ) []⋈ (λ A _ ih → A ∷ˡ ih) Γ

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
      Γ ⋈ Δ ≡ θ → Γ ⊢ A `⊗ B → B ∷ A ∷ Δ ⊢ C →
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
      Γ ⋈ Δ ≡ θ → Γ ⊢ A `+ B → A ∷ Δ ⊢ C → B ∷ Δ ⊢ C →
      ------------------------------------------------- (case)
                            θ ⊢ C

  -- RATIO

    `1/_ :
          (n : ℕ) →
       --------------- (1/2+n)
         θ ⊢ `1 `+ `1
     


swap⊗ : [ `ℕ `⊗ `ℝ ] ⊢ `ℝ `⊗ `ℕ
swap⊗ =
  ⋈[]               ⊨`let var z `in
  [ `ℝ ] ₁⋈₂ [ `ℕ ] ⊨`⟨ var z , var z ⟩


swap+ : [ `ℕ `+ `ℝ ] ⊢ `ℝ `+ `ℕ
swap+ =
  ⋈[] ⊨`case var z
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
