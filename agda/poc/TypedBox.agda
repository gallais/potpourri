module poc.TypedBox where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Data.Product
open import Data.Sum

data Ty :      Set
data Fo : Ty → Set

data Ty where
  `Fin      : Nat → Ty
  _`×_ _`→_ : Ty → Ty → Ty
  C[_,_]    : {σ τ : Ty} → Fo σ → Fo τ → Ty

data Fo where
  `Fin : (n : Nat) → Fo (`Fin n)
  _`×_ : {σ τ : Ty} → Fo σ → Fo τ → Fo (σ `× τ)

CTy = List (∃ Fo)
Circuit = CTy → CTy → Set

module _ {I : Set} where

  infixr 2 _∙⊎_
  _∙⊎_ : (I → Set) → (I → Set) → (I → Set)
  (A ∙⊎ B) i = A i ⊎ B i

  infixr 3 _∙×_
  _∙×_ : (I → Set) → (I → Set) → (I → Set)
  (A ∙× B) i = A i × B i

  infixr 1 _∙→_
  _∙→_ : (I → Set) → (I → Set) → (I → Set)
  (A ∙→ B) i = A i → B i

  infix 0 [_]
  [_] : (I → Set) → Set
  [ A ] = ∀ {i} → A i

  infix 4 _⊢_
  _⊢_ : (I → I) → (I → Set) → (I → Set)
  (f ⊢ A) i = A (f i)


data Var : Ty → List Ty → Set where
  z : {σ : Ty}   → [                    Var σ ]
  s : {σ τ : Ty} → [ Var σ ∙→ (τ ∷_) ⊢  Var σ ]

data Tm : Ty → List Ty → Set where
  `var : {σ : Ty} → [ Var σ ∙→ Tm σ ]
  `box : {s t : Ty} {σ : Fo s} {τ : Fo t} →
         [ Tm (s `→ t) ∙→ Tm C[ σ , τ ] ]
  `run : {s t : Ty} {σ : Fo s} {τ : Fo t} →
         [ Tm C[ σ , τ ] ∙→ Tm (s `→ t) ]
  `lam : {σ τ : Ty} →
         [ (σ ∷_) ⊢ Tm τ ∙→ Tm (σ `→ τ) ]
  `app : {σ τ : Ty} →
         [ Tm (σ `→ τ) ∙→ Tm σ ∙→ Tm τ ]

{-
CTy : Set
CTy = List BTy

data FTy : Set where
  lift : BTy → FTy
  _`×_ : FTy → FTy → FTy
  


toCTy : LTy → CTy
toCTy = {!!}

toLTy : CTy → LTy
toLTy = {!!}
-}
