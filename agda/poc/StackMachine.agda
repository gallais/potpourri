module poc.StackMachine where

open import Data.List.Base hiding ([_] ; unfold)
open import Data.Sum
open import Level using (Level ; _⊔_)
open import Function using (flip ; _∘′_)

module _ {I : Set} where

 infixr 5 _⟶_
 infixr 6 _∙⊎_
 infix  8 _⊢_

 _⟶_ :  {ℓ ℓ′ : Level} → (I → Set ℓ) → (I → Set ℓ′) → (I → Set (ℓ′ ⊔ ℓ))
 (S ⟶ T) i = S i → T i

 _∙⊎_ : {ℓ ℓ′ : Level} → (I → Set ℓ) → (I → Set ℓ′) → (I → Set (ℓ′ ⊔ ℓ))
 (S ∙⊎ T) i = S i ⊎ T i

 κ : {ℓ : Level} → Set ℓ → (I → Set ℓ)
 κ S i = S

 [_] :  {ℓ : Level} → (I → Set ℓ) → Set ℓ
 [ T ] = ∀ {i} → T i

 _⊢_ :  {ℓ : Level} → (I → I) → (I → Set ℓ) → (I → Set ℓ)
 (f ⊢ T) i = T (f i)

_─Scoped : Set → Set₁
I ─Scoped = I → List I → Set

module _ {I : Set} where

 data Var : I ─Scoped where
   z : {i : I} →    [          (i ∷_) ⊢ Var i ]
   s : {i j : I} →  [ Var i ⟶  (j ∷_) ⊢ Var i ]

data Type : Set where
  α   : Type
  _⇒_ : Type → Type → Type

data Trm : Type ─Scoped where
  var : ∀ {σ}   → [ Var σ                ⟶ Trm σ       ]
  lam : ∀ {σ τ} → [ (σ ∷_) ⊢ Trm τ       ⟶ Trm (σ ⇒ τ) ]
  app : ∀ {σ τ} → [ Trm (σ ⇒ τ) ⟶ Trm σ ⟶ Trm τ       ]

data Val : Type ─Scoped
data Neu : Type ─Scoped
data Sub : List Type → List Type → Set
record Cls (T : Type ─Scoped) σ Γ : Set

data Val where
  lam : ∀ {Γ Δ σ τ} → Sub Γ Δ → Trm τ (σ ∷ Γ) → Val (σ ⇒ τ) Δ
  neu : ∀ {σ}       → [ Neu σ          ⟶ Val σ       ]

data Neu where
  var : ∀ {σ}   → [ Var σ                ⟶ Neu σ ]
  app : ∀ {σ τ} → [ Neu (σ ⇒ τ) ⟶ Val σ ⟶ Neu τ ]

data Sub where
  id  : ∀ {Γ}   → Sub Γ Γ
  _∙_ : ∀ {Γ σ} → [ Sub Γ ⟶ Val σ ⟶ Sub (σ ∷ Γ) ]

record Cls T σ Γ where
  constructor <_[_]>
  field {src} : List Type
        cls   : T σ src
        sub   : Sub src Γ

data Stk : Type → List Type → Type ─Scoped where
  []  : ∀ {σ Γ}     → Stk σ Γ σ Γ
  apl : ∀ {σ τ ν Γ} → [ Stk ν Γ τ ⟶ Cls Trm σ   ⟶ Stk ν Γ (σ ⇒ τ)    ]
  apr : ∀ {σ τ ν Γ} → [ Val (σ ⇒ τ) ⟶ Stk ν Γ τ ⟶ Stk ν Γ σ          ]

record Machine σ Γ : Set where
  constructor <_[_]∣_>
  field {src} : List Type
        {tgt} : List Type
        {typ} : Type
        trm   : Trm typ src
        sub   : Sub src tgt
        stk   : Stk σ Γ typ tgt

step↑ : ∀ {ν Γ σ} → [ Val σ ⟶ Stk ν Γ σ ⟶ κ (Val ν Γ ⊎ Machine ν Γ) ]
step↑ val []                     = inj₁ val
step↑ val (apl stk < t [ sub ]>) = inj₂ < t [ sub ]∣ (apr val stk) >
step↑ val (apr (lam env b) stk)  = inj₂ < b [ env ∙ val ]∣ stk >
step↑ val (apr (neu t)     stk)  = step↑ (neu (app t val)) stk

step↓ : ∀ {σ} → [ Machine σ ⟶ Val σ ∙⊎ Machine σ ]
step↓ < var k     [ id      ]∣ stk > = step↑ (neu (var k)) stk
step↓ < var z     [ sub ∙ v ]∣ stk > = step↑ v stk
step↓ < var (s k) [ sub ∙ v ]∣ stk > = inj₂ < var k [ sub ]∣ stk >
step↓ < lam b     [ sub     ]∣ stk > = step↑ (lam sub b) stk
step↓ < app f t   [ sub     ]∣ stk > = inj₂ < f [ sub ]∣ (apl stk < t [ sub ]>) >

open import Size

data    Trace (A B : Set) (i : Size) : Set
record ∞Trace (A B : Set) (i : Size) : Set

data Trace A B i where
  step : A → ∞Trace A B i → Trace A B i
  done : B → Trace A B i

record ∞Trace A B i where
  coinductive; constructor delay
  field force : {j : Size< i} → Trace A B j

module _ {A B : Set} (next : A → B ⊎ A) where

  unfold  : {i : Size} → A → Trace A B i
  ∞unfold : {i : Size} → A → ∞Trace A B i

  unfold seed with next seed
  ... | inj₁ b = done b
  ... | inj₂ a = step a (∞unfold a)

  ∞Trace.force (∞unfold seed) = unfold seed

eval : ∀ {σ} → Trm σ [] → Trace (Machine σ []) (Val σ []) ∞
eval t = unfold step↓ < t [ id ]∣ [] >

