module Data.Functor where

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.List
open import Function
open import Relation.Nullary
open import lib.Nullary
open import Relation.Binary.PropositionalEquality

infixr 3 _`+_ _`*_
data Desc : Set₁ where
  `K   : (A : Set) → Desc       -- constant
  `X   : Desc                   -- recursive
  `L   : Desc                   -- leaf
  _`+_ : (d₁ d₂ : Desc) → Desc  -- disjunction
  _`*_ : (d₁ d₂ : Desc) → Desc  -- conjunction

module ValueConstrained
       (Alphabet : Set)
       (_≤_  : (a b : Alphabet) → Set)
       (_≟_  : (a b : Alphabet) → Dec (a ≡ b))
       (_≤?_ : (a b : Alphabet) → Dec (a ≤ b))
       where

  open import RegExp.Search Alphabet _≤_ _≟_ _≤?_

  ⟦_⟧ : (d : Desc) (X : (e f : RegExp) → Set) (e f : RegExp) → Set
  ⟦ `K A     ⟧ X e f = A × e ≡ f
  ⟦ `X       ⟧ X e f = X e f
  ⟦ `L       ⟧ X e f = Σ[ a ∈ Alphabet ] (e ⟪ a) ≡ f
  ⟦ d₁ `+ d₂ ⟧ X e f = ⟦ d₁ ⟧ X e f ⊎ ⟦ d₂ ⟧ X e f
  ⟦ d₁ `* d₂ ⟧ X e f = Σ[ ef ∈ RegExp ] ⟦ d₁ ⟧ X e ef × ⟦ d₂ ⟧ X ef f

  data `μ (d : Desc) (e f : RegExp) : Set where
    ⟨_⟩ : ⟦ d ⟧ (`μ d) e f → `μ d e f

  μ : (d : Desc) (e : RegExp) → Set
  μ d e = Σ[ f ∈ RegExp ] ([] ∈ f) × `μ d e f


open import Data.Nat

module TypeConstrained (n : ℕ) where

  open import Data.Empty
  open import Data.Nat as Nat
  open import Data.Fin as Fin
  open import Relation.Binary.On

  suc-inj : {n : ℕ} (a b : Fin n) (eq : (Fin (suc n) ∋ suc a) ≡ suc b) → a ≡ b
  suc-inj b .b refl = refl 

  infix 1 Fin_≟_
  Fin_≟_ : {n : ℕ} (a b : Fin n) → Dec (a ≡ b)
  Fin zero  ≟ zero  = yes refl
  Fin zero  ≟ suc b = no (λ ())
  Fin suc a ≟ zero  = no (λ ())
  Fin suc a ≟ suc b = dec (Fin_≟_ a b) (yes ∘ cong suc) (λ ¬eq → no $ ¬eq ∘ suc-inj _ _)

  open import RegExp.Search (Fin n) Fin._≤_ Fin_≟_ (decidable toℕ Nat._≤_ Nat._≤?_) public

  ⟦_⟧ : (d : Desc) (ρ : Fin n → Set) (X : (e f : RegExp) → Set) (e f : RegExp) → Set
  ⟦ `K A     ⟧ ρ X e f = A × e ≡ f
  ⟦ `X       ⟧ ρ X e f = X e f
  ⟦ `L       ⟧ ρ X e f = Σ[ k ∈ Fin n ] Σ[ a ∈ ρ k ] (e ⟪ k) ≡ f
  ⟦ d₁ `+ d₂ ⟧ ρ X e f = ⟦ d₁ ⟧ ρ X e f ⊎ ⟦ d₂ ⟧ ρ X e f
  ⟦ d₁ `* d₂ ⟧ ρ X e f = Σ[ ef ∈ RegExp ] ⟦ d₁ ⟧ ρ X e ef × ⟦ d₂ ⟧ ρ X ef f

  data `μ (d : Desc) (ρ : Fin n → Set) (e f : RegExp) : Set where
    ⟨_⟩ : ⟦ d ⟧ ρ (`μ d ρ) e f → `μ d ρ e f

  μ : (d : Desc) (ρ : Fin n → Set) (e : RegExp) → Set
  μ d ρ e = Σ[ f ∈ RegExp ] ([] ∈ f) × `μ d ρ e f