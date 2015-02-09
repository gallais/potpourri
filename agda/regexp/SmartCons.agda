open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.Empty
open import Data.Bool     hiding (_≟_)
open import Data.Maybe    as Maybe
open import Data.Product  as Product
open import Data.List     as List    using (List ; [] ; _∷_)

open import lib.Nullary
open import Function

module regexp.SmartCons
       (Alphabet : Set)
       (_≟_ : (a b : Alphabet) → Dec (a ≡ b))
       where

  import regexp.RegExp
  module RE = regexp.RegExp Alphabet _≟_
  open RE public

  infixr 5 _`∣_
  infixr 6 _`∙_
  infix  7 _`⋆

  -- Smart constructors.

  _`∣_ : (e₁ e₂ : RegExp) → RegExp
  ∅  `∣ e₂ = e₂
  e₁ `∣ ∅  = e₁
  e₁ `∣ e₂ = e₁ ∣ e₂

  _`∙_ : (e₁ e₂ : RegExp) → RegExp
  ∅  `∙ e₂ = ∅
  e₁ `∙ ∅  = ∅
  e₁ `∙ e₂ = e₁ ∙ e₂

  _`⋆ : RegExp → RegExp
  ∅ `⋆ = ε
  e `⋆ = e ⋆

  -- proof that they are semantics preserving
  -- complete:

  `∣-complete : (e₁ e₂ : RegExp) {xs : List Alphabet} →
                xs ∈ e₁ ∣ e₂ → xs ∈ e₁ `∣ e₂
  `∣-complete ∅ e (() ∣₁ .e)
  `∣-complete ∅ e (.∅ ∣₂ pr) = pr
  `∣-complete ε ∅ (pr ∣₁ .∅) = pr
  `∣-complete ε ∅ (.ε ∣₂ ())
  `∣-complete ε ε pr = pr
  `∣-complete ε ─ pr = pr
  `∣-complete ε [ a ] pr = pr
  `∣-complete ε (e₂ ∣ e₃) pr = pr
  `∣-complete ε (e₂ ∙ e₃) pr = pr
  `∣-complete ε (e₂ ⋆) pr = pr
  `∣-complete ─ ∅ (pr ∣₁ .∅) = pr
  `∣-complete ─ ∅ (.─ ∣₂ ())
  `∣-complete ─ ε pr = pr
  `∣-complete ─ ─ pr = pr
  `∣-complete ─ [ a ] pr = pr
  `∣-complete ─ (e₂ ∣ e₃) pr = pr
  `∣-complete ─ (e₂ ∙ e₃) pr = pr
  `∣-complete ─ (e₂ ⋆) pr = pr
  `∣-complete [ a ] ∅ (pr ∣₁ .∅) = pr
  `∣-complete [ a ] ∅ (._ ∣₂ ())
  `∣-complete [ a ] ε pr = pr
  `∣-complete [ a ] ─ pr = pr
  `∣-complete [ a ] [ a₁ ] pr = pr
  `∣-complete [ a ] (e₂ ∣ e₃) pr = pr
  `∣-complete [ a ] (e₂ ∙ e₃) pr = pr
  `∣-complete [ a ] (e₂ ⋆) pr = pr
  `∣-complete (e₁ ∣ e₂) ∅ (pr ∣₁ .∅) = pr
  `∣-complete (e₁ ∣ e₂) ∅ (._ ∣₂ ())
  `∣-complete (e₁ ∣ e₂) ε pr = pr
  `∣-complete (e₁ ∣ e₂) ─ pr = pr
  `∣-complete (e₁ ∣ e₂) [ a ] pr = pr
  `∣-complete (e₁ ∣ e₂) (e₃ ∣ e₄) pr = pr
  `∣-complete (e₁ ∣ e₂) (e₃ ∙ e₄) pr = pr
  `∣-complete (e₁ ∣ e₂) (e₃ ⋆) pr = pr
  `∣-complete (e₁ ∙ e₂) ∅ (pr ∣₁ .∅) = pr
  `∣-complete (e₁ ∙ e₂) ∅ (._ ∣₂ ())
  `∣-complete (e₁ ∙ e₂) ε pr = pr
  `∣-complete (e₁ ∙ e₂) ─ pr = pr
  `∣-complete (e₁ ∙ e₂) [ a ] pr = pr
  `∣-complete (e₁ ∙ e₂) (e₃ ∣ e₄) pr = pr
  `∣-complete (e₁ ∙ e₂) (e₃ ∙ e₄) pr = pr
  `∣-complete (e₁ ∙ e₂) (e₃ ⋆) pr = pr
  `∣-complete (e ⋆) ∅ (pr ∣₁ .∅) = pr
  `∣-complete (e ⋆) ∅ (._ ∣₂ ())
  `∣-complete (e₁ ⋆) ε pr = pr
  `∣-complete (e₁ ⋆) ─ pr = pr
  `∣-complete (e₁ ⋆) [ a ] pr = pr
  `∣-complete (e₁ ⋆) (e₂ ∣ e₃) pr = pr
  `∣-complete (e₁ ⋆) (e₂ ∙ e₃) pr = pr
  `∣-complete (e₁ ⋆) (e₂ ⋆) pr = pr

  `∙-complete : (e₁ e₂ : RegExp) {xs : List Alphabet} →
                xs ∈ e₁ ∙ e₂ → xs ∈ e₁ `∙ e₂
  `∙-complete ∅ e (() ∙ pr ⇚ eq)
  `∙-complete ε ∅ (pr ∙ () ⇚ eq)
  `∙-complete ε ε pr = pr
  `∙-complete ε ─ pr = pr
  `∙-complete ε [ a ] pr = pr
  `∙-complete ε (e₂ ∣ e₃) pr = pr
  `∙-complete ε (e₂ ∙ e₃) pr = pr
  `∙-complete ε (e₂ ⋆) pr = pr
  `∙-complete ─ ∅ (pr ∙ () ⇚ eq)
  `∙-complete ─ ε pr = pr
  `∙-complete ─ ─ pr = pr
  `∙-complete ─ [ a ] pr = pr
  `∙-complete ─ (e₂ ∣ e₃) pr = pr
  `∙-complete ─ (e₂ ∙ e₃) pr = pr
  `∙-complete ─ (e₂ ⋆) pr = pr
  `∙-complete [ a ] ∅ (pr ∙ () ⇚ eq)
  `∙-complete [ a ] ε pr = pr
  `∙-complete [ a ] ─ pr = pr
  `∙-complete [ a ] [ a₁ ] pr = pr
  `∙-complete [ a ] (e₂ ∣ e₃) pr = pr
  `∙-complete [ a ] (e₂ ∙ e₃) pr = pr
  `∙-complete [ a ] (e₂ ⋆) pr = pr
  `∙-complete (e₁ ∣ e₂) ∅ (pr ∙ () ⇚ eq)
  `∙-complete (e₁ ∣ e₂) ε pr = pr
  `∙-complete (e₁ ∣ e₂) ─ pr = pr
  `∙-complete (e₁ ∣ e₂) [ a ] pr = pr
  `∙-complete (e₁ ∣ e₂) (e₃ ∣ e₄) pr = pr
  `∙-complete (e₁ ∣ e₂) (e₃ ∙ e₄) pr = pr
  `∙-complete (e₁ ∣ e₂) (e₃ ⋆) pr = pr
  `∙-complete (e₁ ∙ e₂) ∅ (pr ∙ () ⇚ eq)
  `∙-complete (e₁ ∙ e₂) ε pr = pr
  `∙-complete (e₁ ∙ e₂) ─ pr = pr
  `∙-complete (e₁ ∙ e₂) [ a ] pr = pr
  `∙-complete (e₁ ∙ e₂) (e₃ ∣ e₄) pr = pr
  `∙-complete (e₁ ∙ e₂) (e₃ ∙ e₄) pr = pr
  `∙-complete (e₁ ∙ e₂) (e₃ ⋆) pr = pr
  `∙-complete (e₁ ⋆) ∅ (pr ∙ () ⇚ eq)
  `∙-complete (e₁ ⋆) ε pr = pr
  `∙-complete (e₁ ⋆) ─ pr = pr
  `∙-complete (e₁ ⋆) [ a ] pr = pr
  `∙-complete (e₁ ⋆) (e₂ ∣ e₃) pr = pr
  `∙-complete (e₁ ⋆) (e₂ ∙ e₃) pr = pr
  `∙-complete (e₁ ⋆) (e₂ ⋆) pr = pr

  `⋆-complete : (e : RegExp) {xs : List Alphabet} →
                xs ∈ e ⋆ → xs ∈ e `⋆
  `⋆-complete ∅ (pr ∣₁ ._ ⋆) = pr
  `⋆-complete ∅ (._ ∣₂ (() ∙ _ ⇚ _) ⋆)
  `⋆-complete ε pr = pr
  `⋆-complete ─ pr = pr
  `⋆-complete [ a ] pr = pr
  `⋆-complete (e ∣ e₁) pr = pr
  `⋆-complete (e ∙ e₁) pr = pr
  `⋆-complete (e ⋆) pr = pr

  -- sound;:

  `∣-sound : (e₁ e₂ : RegExp) {xs : List Alphabet} →
             xs ∈ e₁ `∣ e₂ → xs ∈ e₁ ∣ e₂
  `∣-sound ∅ e pr = ∅ ∣₂ pr
  `∣-sound ε ∅ pr = pr ∣₁ ∅
  `∣-sound ε ε pr = pr
  `∣-sound ε ─ pr = pr
  `∣-sound ε [ a ] pr = pr
  `∣-sound ε (e₂ ∣ e₃) pr = pr
  `∣-sound ε (e₂ ∙ e₃) pr = pr
  `∣-sound ε (e₂ ⋆) pr = pr
  `∣-sound ─ ∅ pr = pr ∣₁ ∅
  `∣-sound ─ ε pr = pr
  `∣-sound ─ ─ pr = pr
  `∣-sound ─ [ a ] pr = pr
  `∣-sound ─ (e₂ ∣ e₃) pr = pr
  `∣-sound ─ (e₂ ∙ e₃) pr = pr
  `∣-sound ─ (e₂ ⋆) pr = pr
  `∣-sound [ a ] ∅ pr = pr ∣₁ ∅
  `∣-sound [ a ] ε pr = pr
  `∣-sound [ a ] ─ pr = pr
  `∣-sound [ a ] [ a₁ ] pr = pr
  `∣-sound [ a ] (e₂ ∣ e₃) pr = pr
  `∣-sound [ a ] (e₂ ∙ e₃) pr = pr
  `∣-sound [ a ] (e₂ ⋆) pr = pr
  `∣-sound (e₁ ∣ e₂) ∅ pr = pr ∣₁ ∅
  `∣-sound (e₁ ∣ e₂) ε pr = pr
  `∣-sound (e₁ ∣ e₂) ─ pr = pr
  `∣-sound (e₁ ∣ e₂) [ a ] pr = pr
  `∣-sound (e₁ ∣ e₂) (e₃ ∣ e₄) pr = pr
  `∣-sound (e₁ ∣ e₂) (e₃ ∙ e₄) pr = pr
  `∣-sound (e₁ ∣ e₂) (e₃ ⋆) pr = pr
  `∣-sound (e₁ ∙ e₂) ∅ pr = pr ∣₁ ∅
  `∣-sound (e₁ ∙ e₂) ε pr = pr
  `∣-sound (e₁ ∙ e₂) ─ pr = pr
  `∣-sound (e₁ ∙ e₂) [ a ] pr = pr
  `∣-sound (e₁ ∙ e₂) (e₃ ∣ e₄) pr = pr
  `∣-sound (e₁ ∙ e₂) (e₃ ∙ e₄) pr = pr
  `∣-sound (e₁ ∙ e₂) (e₃ ⋆) pr = pr
  `∣-sound (e₁ ⋆) ∅ pr = pr ∣₁ ∅
  `∣-sound (e₁ ⋆) ε pr = pr
  `∣-sound (e₁ ⋆) ─ pr = pr
  `∣-sound (e₁ ⋆) [ a ] pr = pr
  `∣-sound (e₁ ⋆) (e₂ ∣ e₃) pr = pr
  `∣-sound (e₁ ⋆) (e₂ ∙ e₃) pr = pr
  `∣-sound (e₁ ⋆) (e₂ ⋆) pr = pr

  `∙-sound : (e₁ e₂ : RegExp) {xs : List Alphabet} →
             xs ∈ e₁ `∙ e₂ → xs ∈ e₁ ∙ e₂
  `∙-sound ∅ e ()
  `∙-sound ε ∅ ()
  `∙-sound ε ε pr = pr
  `∙-sound ε ─ pr = pr
  `∙-sound ε [ a ] pr = pr
  `∙-sound ε (e₂ ∣ e₃) pr = pr
  `∙-sound ε (e₂ ∙ e₃) pr = pr
  `∙-sound ε (e₂ ⋆) pr = pr
  `∙-sound ─ ∅ ()
  `∙-sound ─ ε pr = pr
  `∙-sound ─ ─ pr = pr
  `∙-sound ─ [ a ] pr = pr
  `∙-sound ─ (e₂ ∣ e₃) pr = pr
  `∙-sound ─ (e₂ ∙ e₃) pr = pr
  `∙-sound ─ (e₂ ⋆) pr = pr
  `∙-sound [ a ] ∅ ()
  `∙-sound [ a ] ε pr = pr
  `∙-sound [ a ] ─ pr = pr
  `∙-sound [ a ] [ a₁ ] pr = pr
  `∙-sound [ a ] (e₂ ∣ e₃) pr = pr
  `∙-sound [ a ] (e₂ ∙ e₃) pr = pr
  `∙-sound [ a ] (e₂ ⋆) pr = pr
  `∙-sound (e₁ ∣ e₂) ∅ ()
  `∙-sound (e₁ ∣ e₂) ε pr = pr
  `∙-sound (e₁ ∣ e₂) ─ pr = pr
  `∙-sound (e₁ ∣ e₂) [ a ] pr = pr
  `∙-sound (e₁ ∣ e₂) (e₃ ∣ e₄) pr = pr
  `∙-sound (e₁ ∣ e₂) (e₃ ∙ e₄) pr = pr
  `∙-sound (e₁ ∣ e₂) (e₃ ⋆) pr = pr
  `∙-sound (e₁ ∙ e₂) ∅ ()
  `∙-sound (e₁ ∙ e₂) ε pr = pr
  `∙-sound (e₁ ∙ e₂) ─ pr = pr
  `∙-sound (e₁ ∙ e₂) [ a ] pr = pr
  `∙-sound (e₁ ∙ e₂) (e₃ ∣ e₄) pr = pr
  `∙-sound (e₁ ∙ e₂) (e₃ ∙ e₄) pr = pr
  `∙-sound (e₁ ∙ e₂) (e₃ ⋆) pr = pr
  `∙-sound (e₁ ⋆) ∅ pr = (ε ∣₁ _ ⋆) ∙ pr ⇚ refl
  `∙-sound (e₁ ⋆) ε pr = pr
  `∙-sound (e₁ ⋆) ─ pr = pr
  `∙-sound (e₁ ⋆) [ a ] pr = pr
  `∙-sound (e₁ ⋆) (e₂ ∣ e₃) pr = pr
  `∙-sound (e₁ ⋆) (e₂ ∙ e₃) pr = pr
  `∙-sound (e₁ ⋆) (e₂ ⋆) pr = pr

  `⋆-sound : (e : RegExp) {xs : List Alphabet} →
             xs ∈ e `⋆ → xs ∈ e ⋆
  `⋆-sound ∅ pr = pr ∣₁ _ ⋆
  `⋆-sound ε pr = pr
  `⋆-sound ─ pr = pr
  `⋆-sound [ a ] pr = pr
  `⋆-sound (e ∣ e₁) pr = pr
  `⋆-sound (e ∙ e₁) pr = pr
  `⋆-sound (e ⋆) pr = pr