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

  infixr 2 κ_
  κ_ : Set → (I → Set)
  (κ A) i = A

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
  z : {σ : Ty}   → [           (σ ∷_) ⊢ Var σ ]
  s : {σ τ : Ty} → [ Var σ ∙→  (τ ∷_) ⊢ Var σ ]

module Term (𝓖 : {s t : Ty} (σ : Fo s) (τ : Fo t) → Set) where

  data Tm : Ty → List Ty → Set where
    `gat : {s t : Ty} {σ : Fo s} {τ : Fo t} →
           [ κ 𝓖 σ τ ∙→ Tm C[ σ , τ ] ]
    `box : {s t : Ty} {σ : Fo s} {τ : Fo t} →
           [ Tm (s `→ t) ∙→ Tm C[ σ , τ ] ]
    `run : {s t : Ty} {σ : Fo s} {τ : Fo t} →
           [ Tm C[ σ , τ ] ∙→ Tm (s `→ t) ]

    `var : {σ : Ty} → [ Var σ ∙→ Tm σ ]
    `lam : {σ τ : Ty} →
           [ (σ ∷_) ⊢ Tm τ ∙→ Tm (σ `→ τ) ]
    `app : {σ τ : Ty} →
           [ Tm (σ `→ τ) ∙→ Tm σ ∙→ Tm τ ]
    `fst : {σ τ : Ty} →
           [ Tm (σ `× τ) ∙→ Tm σ ]
    `snd : {σ τ : Ty} →
           [ Tm (σ `× τ) ∙→ Tm τ ]
    `prd : {σ τ : Ty} →
           [ Tm σ ∙→ Tm τ ∙→ Tm (σ `× τ) ]
    `zro : {n : Nat} →
           [ Tm (`Fin (suc n)) ]
    `suc : {n : Nat} →
           [ Tm (`Fin n) ∙→ Tm (`Fin (suc n)) ]
    `cas : {n : Nat} {σ : Ty} →
           [ Tm (`Fin (suc n)) ∙→ Tm σ ∙→ Tm (`Fin n `→ σ) ∙→ Tm σ ]
    `bm! : {n : Nat} {σ : Ty} →
           [ Tm (`Fin 0) ∙→ Tm σ ]

  `swap : {s t : Ty} {σ : Fo s} {τ : Fo t} → [ Tm C[ σ `× τ , τ `× σ ] ]
  `swap = `box (`lam (`prd (`snd (`var z)) (`fst (`var z))))

  `if : {σ : Ty} → [ Tm (`Fin 2) ] → [ Tm σ ] → [ Tm σ ] → [ Tm σ ]
  `if b l r = `cas b l (`lam r)
