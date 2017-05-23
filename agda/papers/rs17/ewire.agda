-- The content of this module is based on:
-- Classical control and quantum circuits in enriched category theory
-- by Mathys Rennela and Sam Staton

module papers.rs17.ewire where

data QWTy : Set where
  I   : QWTy
  _⊗_ : QWTy → QWTy → QWTy
  𝟙 𝟚 : QWTy
  ℚ    : QWTy

data CWTy : QWTy → Set where
  instance
    I   : CWTy I
    _⊗_ : {a b : QWTy} → CWTy a → CWTy b → CWTy (a ⊗ b)
    𝟙   : CWTy 𝟙
    𝟚   : CWTy 𝟚

infixr 5 _`→_
data Ty : Set where
  `⟨⟩    : Ty
  _`×_   : Ty → Ty → Ty
  `1 `2  : Ty
  _`→_   : Ty → Ty → Ty
  T      : Ty → Ty
  C[_,_] : QWTy → QWTy → Ty

data CTy : Ty → Set where
  instance
    `⟨⟩  : CTy `⟨⟩
    _`×_ : {a b : Ty} → CTy a → CTy b → CTy (a `× b)
    𝟙    : CTy `1
    𝟚    : CTy `1

it : {A : Set} → {{a : A}} → A
it {{a}} = a

qwty : {W : Ty} → CTy W → QWTy
qwty `⟨⟩    = I
qwty (σ `× τ) = qwty σ ⊗ qwty τ
qwty 𝟙      = 𝟙
qwty 𝟚      = 𝟚

ty : {W : QWTy} → CWTy W → Ty
ty I       = `⟨⟩
ty (a ⊗ b) = ty a `× ty b
ty 𝟙       = `1
ty 𝟚       = `2

open import Data.List.Base

infix 1 _⇒_
infixr 5 _,_
data _⇒_ : QWTy → List QWTy → Set where
  <>  : 𝟙 ⇒ []
  id  : {a : QWTy} → a ⇒ a ∷ []
  _,_ : {a b : QWTy} {vs ws : List QWTy} →
        a ⇒ vs → b ⇒ ws →
        a ⊗ b ⇒ vs ++ ws

infix 1 _∋_
data _∋_ {A : Set} : List A → A → Set where
  z : {Γ : List A} {σ : A} → σ ∷ Γ ∋ σ
  s : {Γ : List A} {σ τ : A} → Γ ∋ σ → τ ∷ Γ ∋ σ

module Terms (𝓖 : QWTy → QWTy → Set) where

  infix 1 _∣_⊢_ _⊢_
  infixr 5 box_↦_
  infixr 5 _←_>_ gate_$_ 

  data _∣_⊢_ (Γ : List Ty) : (Ω : List QWTy) (W : QWTy) → Set
  data _⊢_ (Γ : List Ty) : Ty → Set

  data _∣_⊢_ Γ where
    _←_>_  : {Ω Ω₁ Ω₂ : List QWTy} {W₁ W₂ : QWTy} →
             W₁ ⇒ Ω → Γ ∣ Ω₁ ⊢ W₁ → Γ ∣ Ω ++ Ω₂ ⊢ W₂ →
             Γ ∣ Ω₁ ++ Ω₂ ⊢ W₂

    output : {Ω : List QWTy} {W : QWTy} →
             W ⇒ Ω → Γ ∣ Ω ⊢ W

    gate_$_ : {Ω₁ : List QWTy} {W₁ W₂ : QWTy} →
              𝓖 W₁ W₂ → W₁ ⇒ Ω₁ → Γ ∣ Ω₁ ⊢ W₂

    unbox_as_ : {W₁ W₂ : QWTy} {Ω : List QWTy} →
                Γ ⊢ C[ W₁ , W₂ ] → W₁ ⇒ Ω → Γ ∣ Ω ⊢ W₂

    init : {W : QWTy} (σ : CWTy W) →
           Γ ⊢ ty σ → Γ ∣ [] ⊢ W

    lift : {Ω Ω′ : List QWTy} {W W′ : QWTy} (σ : CWTy W) →
           W ⇒ Ω → ty σ ∷ Γ ∣ Ω′ ⊢ W′ → Γ ∣ Ω ++ Ω′ ⊢ W′

  infixr 5 _,_
  data _⊢_ Γ where
    run : {σ : Ty} → (W : CTy σ) →
          Γ ∣ [] ⊢ qwty W → Γ ⊢ T σ

    box_↦_ : {Ω : List QWTy} {W₁ W₂ : QWTy} →
             W₁ ⇒ Ω → Γ ∣ Ω ⊢ W₂ → Γ ⊢ C[ W₁ , W₂ ]

    var    : {σ : Ty} → Γ ∋ σ → Γ ⊢ σ
    lam    : {σ τ : Ty} → σ ∷ Γ ⊢ τ → Γ ⊢ σ `→ τ
    app    : {σ τ : Ty} → Γ ⊢ σ `→ τ → Γ ⊢ σ → Γ ⊢ τ
    unit   : Γ ⊢ `1
    true   : Γ ⊢ `2
    false  : Γ ⊢ `2
    _,_    : {σ τ : Ty} → Γ ⊢ σ → Γ ⊢ τ → Γ ⊢ σ `× τ
    fst    : {σ τ : Ty} → Γ ⊢ σ `× τ → Γ ⊢ σ
    snd    : {σ τ : Ty} → Γ ⊢ σ `× τ → Γ ⊢ τ
    return : {σ : Ty} → Γ ⊢ σ → Γ ⊢ T σ
    _then_ : {σ τ : Ty} → Γ ⊢ T σ → σ ∷ Γ ⊢ T τ → Γ ⊢ T τ


module Example where

  data Gate : QWTy → QWTy → Set where
    init₀ : Gate 𝟙 ℚ
    H     : Gate ℚ ℚ
    meas  : Gate ℚ 𝟚

  open Terms Gate

  flip : [] ∣ [] ⊢ 𝟚
  flip = id ← gate init₀ $ <>
       > id ← gate H     $ id
       > id ← gate meas  $ id
       > output id

  ⌊_⌋ : QWTy → QWTy
  ⌊ a ⊗ b ⌋ = ⌊ a ⌋ ⊗ ⌊ b ⌋
  ⌊ ℚ     ⌋ = 𝟚
  ⌊ a     ⌋ = a

  gmeas : (W : QWTy) → [] ⊢ C[ W , ⌊ W ⌋ ]
  gmeas I       = box id ↦ output id
  gmeas (V ⊗ W) = box (id , id)
                ↦ id ← unbox (gmeas V) as id
                > {!!} {- stuck -}
  gmeas 𝟙       = box <> ↦ output <>
  gmeas 𝟚       = box id ↦ output id
  gmeas ℚ       = box id ↦ gate meas $ id
