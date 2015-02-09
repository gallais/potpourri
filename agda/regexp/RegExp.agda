open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.Empty
open import Data.Bool     hiding (_≟_)
open import Data.Maybe    as Maybe
open import Data.Product  as Product
open import Data.List     as List    using (List ; [] ; _∷_)

open import lib.Nullary
open import Function

module regexp.RegExp (Alphabet : Set)
       (_≟_ : (a b : Alphabet) → Dec (a ≡ b))
       where

  infixr 5 _∣_
  infixr 6 _∙_
  infix  7 _⋆

  -- inductive definition of regular expressions
  -- on the alphabet Alphabet

  data RegExp : Set where
    ∅   : RegExp
    ε   : RegExp
    ─   : RegExp
    [_] : (a : Alphabet) → RegExp
    _∣_ : (e₁ e₂ : RegExp) → RegExp
    _∙_ : (e₁ e₂ : RegExp) → RegExp
    _⋆  : (e : RegExp) → RegExp

  -- Extra notions encoded using the existing language

  _+ : (e : RegExp) → RegExp
  e + = e ∙ e ⋆

  _⁇ : (e : RegExp) → RegExp
  e ⁇ = ε ∣ e

  -- semantics in terms of words (lists of letters
  -- in Alphabet)

  infix 3 _∈_
  data _∈_ : (xs : List Alphabet) (e : RegExp) → Set where
    ε     : [] ∈ ε
    ─     : {a : Alphabet} → List.[ a ] ∈ ─
    [_]   : (a : Alphabet) → List.[ a ] ∈ RegExp.[ a ]
    _∣₁_  : {xs : List Alphabet} {e : RegExp} (pr : xs ∈ e) (f : RegExp) → xs ∈ e ∣ f
    _∣₂_  : {xs : List Alphabet} (e : RegExp) {f : RegExp} (pr : xs ∈ f) → xs ∈ e ∣ f
    _∙_⇚_ : {xs ys zs : List Alphabet} {e f : RegExp}
            (pr₁ : xs ∈ e) (pr₂ : ys ∈ f) (eq : zs ≡ xs List.++ ys) → zs ∈ e ∙ f
    _⋆    : {xs : List Alphabet} {e : RegExp} →
            xs ∈ ε ∣ e ∙ e ⋆ → xs ∈ e ⋆