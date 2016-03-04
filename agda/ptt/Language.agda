module ptt.Language where

open import Data.Nat
open import Data.Product
open import ptt.Context as C hiding (Context)

infixr 5 _`+_ _`⊗_
data Type : Set where
  -- base types
  `𝔹 `ℕ `ℝ `0 `1 : Type
  -- sum type
  _`+_ : (A B : Type) → Type
  -- tensor type
  _`⊗_ : (A B : Type) → Type

`2 : Type
`2 = `1 `+ `1

`[_]∙_ : ℕ → Type → Type
`[ 0     ]∙ A = `0
`[ 1     ]∙ A = A
`[ suc n ]∙ A = A `+ `[ n ]∙ A

`[_] : ℕ → Type
`[ n ] = `[ n ]∙ `1

_# : Type → Type
A # = A `+ `1

Context = C.Context Type

-- Terms
infix 1 _⊢_ _⊢_∋_≤_ _⊢_∋_≡_
infixr 5 _⊨`let_`in_
infix 10 _⊨`⟨_,_⟩ _↓ _↑


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

  -- COMPLEMENTARY
    `inlr :
      {A B : Type} (s : θ ⊢ A #) (t : θ ⊢ B #) →
      θ ⊢ `2 ∋ s ↓ ≡ t ↑ →
      ------------------------------------------------
                      θ ⊢ A `+ B

  -- PROJECTION
    `left :
      {A B : Type} (t : θ ⊢ A `+ B) → θ ⊢ `2 ∋ inl? t ≡ ⊤ →
      -------------------------------------------------
                       θ ⊢ A

  -- INSTRUMENT

    `instr :
      {A : Type} (n : ℕ) → [ A ] ⊢ `[ n ] → θ ⊢ A →
      -------------------------------------- (instr)
                 θ ⊢ `[ n ]∙ A

  -- RATIO

    `1/_ :
          (n : ℕ) →
       --------------- (1/2+n)
         θ ⊢ `2

    `nrm :
      {A : Type} →
      (n : ℕ) (t : ε ⊢ A #) → ε ⊢ `1 ∋ `1/ n ≤ t ↓ →
      -------------------------------------------------- (nrm)
                     θ ⊢ A

  -- PARTIAL SUM

    _`⊕_[_,_,_] :
      {A : Type} (s t : θ ⊢ A #)
      (b : θ ⊢ (A `+ A) #) →
      θ ⊢ A # ∋ ⋈ε ⊨ b >>= ▻₁ (var z) ≡ s →
      θ ⊢ A # ∋ ⋈ε ⊨ b >>= ▻₂ (var z) ≡ t →
      ------------------------------------ (⊕)
         θ ⊢ A #

  data _⊢_∋_≤_ (Γ : Context) (A : Type) (s t : Γ ⊢ A #) : Set where
    order :
      (b : Γ ⊢ (A `+ A) #) →
      Γ ⊢ A # ∋ ⋈ε ⊨ b >>= ▻₁ (var z)         ≡ s →
      Γ ⊢ A # ∋ ⋈ε ⊨ b >>= return (∇ (var z)) ≡ t →
      ------------------------------------------------
            Γ ⊢ A ∋ s ≤ t

  data _⊢_∋_↝_ (θ : Context) : (A : Type) (s t : θ ⊢ A) → Set where
    `β⊗ :
      {A B C : Type} {Γ₁ Γ₂ Γ Δ : Context}
      {pr : Γ ⋈ Δ ≡ θ} {prΓ : Γ₁ ⋈ Γ₂ ≡ Γ} {t₁ : Γ₁ ⊢  A} {t₂ : Γ₂ ⊢ B}
      {u : Δ ∙ A ∙ B ⊢ C} →
      θ ⊢ C ∋ pr ⊨`let prΓ ⊨`⟨ t₁ , t₂ ⟩ `in u ↝ {!!}

  data _⊢_∋_≡_ (Γ : Context) : (A : Type) (s t : Γ ⊢ A) → Set where


  ⊤ : {Γ : Context} → Γ ⊢ `2
  ⊤ = return `*
  
  ⊥ : {Γ : Context} {A : Type} → Γ ⊢ A #
  ⊥ = `inr `*



  ∇ : {Γ : Context} {A : Type} → Γ ⊢ A `+ A → Γ ⊢ A
  ∇ t = ⋈ε ⊨`case t
           of var z
           %% var z

  ▻₁ : {Γ : Context} {A B : Type} (t : Γ ⊢ A `+ B) → Γ ⊢ A #
  ▻₁ t = ⋈ε ⊨`case t
            of `inl (var z)
            %% ⊥
            
  ▻₂ : {Γ : Context} {A B : Type} (t : Γ ⊢ A `+ B) → Γ ⊢ B #
  ▻₂ t = ⋈ε ⊨`case t
            of ⊥
            %% `inl (var z)

  _↓ : {Γ : Context} {A : Type} (t : Γ ⊢ A #) → Γ ⊢ `2
  _↓ = inl?

  _↑ : {Γ : Context} {A : Type} (t : Γ ⊢ A #) → Γ ⊢ `2
  t ↑ = ⋈ε ⊨`case t
            of ⊥
            %% ⊤

  return : {Γ : Context} {A : Type} (t : Γ ⊢ A) → Γ ⊢ A #
  return = `inl

  _⊨_>>=_ : {θ Γ Δ : Context} {A B : Type} (j : Γ ⋈ Δ ≡ θ) (t : Γ ⊢ A #) (f : Δ ∙ A ⊢ B #) → θ ⊢ B #
  j ⊨ t >>= f = j ⊨`case t
                  of f
                  %% ⊥

  inl? : {Γ : Context} {A B : Type} (t : Γ ⊢ A `+ B) → Γ ⊢ `2
  inl? t = ⋈ε ⊨`case t
              of ⊤
              %% ⊥

  _‼_ : {θ Γ Δ : Context} {A : Type} (inc : Γ ⋈ Δ ≡ θ) (x : A ∈ Γ) → A ∈ θ
  (inc ∙ˡ A) ‼ z   = z
  (inc ∙ˡ A) ‼ s n = s (inc ‼ n)
  (inc ∙ʳ a) ‼ n   = s (inc ‼ n)

  weaken : {θ Γ Δ : Context} {A : Type} (inc : Γ ⋈ Δ ≡ θ) (t : Γ ⊢ A) → θ ⊢ A
  weaken inc (var x) = var (inc ‼ x)
  weaken inc (`¡ t)  = `¡ (weaken inc t)
  weaken inc `*      = `*
  weaken inc (pr ⊨`⟨ t , u ⟩) =
    let (_ , pr′ , j) = inlineʳ inc pr in pr′ ⊨`⟨ t , weaken j u ⟩
  weaken inc (pr ⊨`let t `in u) =
    let (_ , pr′ , j) = inlineʳ inc pr in pr′ ⊨`let t `in weaken (j ∙ˡ _ ∙ˡ _) u
  weaken inc (`inl t) = `inl (weaken inc t)
  weaken inc (`inr t) = `inr (weaken inc t)
  weaken inc (pr ⊨`case t of l %% r) =
    let (_ , pr′ , j) = inlineʳ inc pr in pr′ ⊨`case t of weaken (j ∙ˡ _) l %% weaken (j ∙ˡ _) r
  weaken inc (`inlr t u eq) = `inlr (weaken inc t) (weaken inc u) {!!}
  weaken inc (`left t eq) = `left (weaken inc t) {!!}
  weaken inc (`instr n p t) = `instr n p (weaken inc t)
  weaken inc (`1/ n) = `1/ n
  weaken inc (`nrm n t le) = `nrm n t le
  weaken inc (t `⊕ u [ b , eqt , equ ]) = weaken inc t `⊕ weaken inc u [ weaken inc b , {!!} , {!!} ]

  weaken-eq : {θ Γ Δ : Context} {A : Type} (inc : Γ ⋈ Δ ≡ θ) {t u : Γ ⊢ A} →
              Γ ⊢ A ∋ t ≡ u → θ ⊢ A ∋ weaken inc t ≡ weaken inc u
  weaken-eq = {!!}

  infix 5 _⊨_∙_
  data Env (θ : Context) : (Γ : Context) → Set where
    ε     : Env θ ε
    _⊨_∙_ : {Γ θ₁ θ₂ : Context} {A : Type} →
            θ₁ ⋈ θ₂ ≡ θ → Env θ₁ Γ → θ₂ ⊢ A → Env θ (Γ ∙ A)

  split-Env : (θ Γ Γ₁ Γ₂ : Context) → Γ₁ ⋈ Γ₂ ≡ Γ → Env θ Γ →
              ∃ λ θ₁ → ∃ λ θ₂ → θ₁ ⋈ θ₂ ≡ θ × Env θ₁ Γ₁ × Env θ₂ Γ₂
  split-Env θ .ε .ε .ε ε ρ = θ , ε , ⋈ε , ε , ε
  split-Env θ (Γ ∙ .a) (Γ₁ ∙ .a) Γ₂ (j ∙ˡ a) (pr ⊨ ρ ∙ t) =
    let (θ₁ , θ₂ , pr₂ , ρ₁ , ρ₂) = split-Env _ Γ Γ₁ Γ₂ j ρ
        (Γ′ , p , j)              = inlineˡ pr pr₂
    in , , p , j ⊨ ρ₁ ∙ t , ρ₂
  split-Env θ (Γ ∙ .a) Γ₁ (Γ₂ ∙ .a) (j ∙ʳ a) (pr ⊨ ρ ∙ t) =
    let (θ₁ , θ₂ , pr₂ , ρ₁ , ρ₂) = split-Env _ Γ Γ₁ Γ₂ j ρ
        (Γ′ , p , j)              = inlineʳ pr pr₂
    in , , p , ρ₁ , j ⊨ ρ₂ ∙ t

  ⟨_⟩_ : {θ Γ : Context} {A : Type} (ρ : Env θ Γ) (x : A ∈ Γ) → θ ⊢ A
  ⟨ pr ⊨ ρ ∙ t ⟩ z   = weaken (symmetry pr) t
  ⟨ pr ⊨ ρ ∙ t ⟩ s x = weaken pr (⟨ ρ ⟩ x)

  extend : {A : Type} {θ Γ : Context} → Env θ Γ → Env (θ ∙ A) (Γ ∙ A)
  extend {A} ρ = ⋈ε ∙ʳ A ⊨ ρ ∙ var z

  subst : {θ Γ : Context} {A : Type} (t : Γ ⊢ A) (ρ : Env θ Γ) → θ ⊢ A
  subst (var x)                     ρ = ⟨ ρ ⟩ x
  subst (`¡ t)                      ρ = `¡ (subst t ρ)
  subst `*                          ρ = `*
  subst (pr ⊨`⟨ t , u ⟩)            ρ =
    let (_ , _ , pr′ , ρ₁ , ρ₂) = split-Env _ _ _ _ pr ρ
    in pr′ ⊨`⟨ subst t ρ₁ , subst u ρ₂ ⟩
  subst (pr ⊨`let t `in u)         ρ =
    let (_ , _ , pr′ , ρ₁ , ρ₂) = split-Env _ _ _ _ pr ρ
    in pr′ ⊨`let subst t ρ₁ `in subst u (extend (extend ρ₂))
  subst (`inl t)                   ρ = `inl (subst t ρ)
  subst (`inr t)                   ρ = `inr (subst t ρ)
  subst (pr ⊨`case t of l %% r)    ρ =
    let (_ , _ , pr′ , ρ₁ , ρ₂) = split-Env _ _ _ _ pr ρ
    in pr′ ⊨`case subst t ρ₁ of subst l (extend ρ₂) %% subst r (extend ρ₂)
  subst (`inlr t u eq)             ρ = `inlr (subst t ρ) (subst u ρ) {!!}
  subst (`left t eq)               ρ = `left (subst t ρ) {!!}
  subst (`instr n p t)             ρ = `instr n p (subst t ρ)
  subst (`1/ n)                    ρ = `1/ n
  subst (`nrm n t le)              ρ = `nrm n t le
  subst (t `⊕ u [ b , eqt , equ ]) ρ = subst t ρ `⊕ subst u ρ [ subst b ρ , {!!} , {!!} ]

  subst-eq : {θ Γ : Context} {A : Type} {t u : Γ ⊢ A} (eq : Γ ⊢ A ∋ t ≡ u) (ρ : Env θ Γ) →
             θ ⊢ A ∋ subst t ρ ≡ subst u ρ
  subst-eq eq ρ = {!!}

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
