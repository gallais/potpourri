module regexp.Examples where

import regexp.Search
open import Function
open import Relation.Nullary

module ExampleNat where

  open import Data.Nat as Nat
  module S = regexp.Search ℕ Nat._≟_
  open S

  0s : RegExp
  0s = [ 0 ] +

  0s1s2s : RegExp
  0s1s2s = 0s ∙ ([ 1 ] ⋆) ∙ ([ 2 ] ⋆)

  open import Data.List

  test : Dec (Substring 0s1s2s (1 ∷ 2 ∷ 0 ∷ 2 ∷ 2 ∷ 0 ∷ 1 ∷ 2 ∷ []))
  test = substring 0s1s2s (1 ∷ 2 ∷ 0 ∷ 2 ∷ 2 ∷ 0 ∷ 1 ∷ 2 ∷ [])

module ExampleString where

  open import Data.Char   as Chr
  open import Data.String as Str
  open import Data.List   as List
  module S = regexp.Search Char Chr._≟_
  open S
  open import Data.Nat

  lit : (str : String) → RegExp
  lit = List.foldr (_∙_ ∘ RE.[_]) ε ∘ Str.toList

  coloUr : RegExp
  coloUr = lit "colo" ∙ (lit "u" ⁇) ∙ lit "r"

  test : Dec $ Substring coloUr $ Str.toList "green is a nice colour, isn't it?"
  test = substring coloUr $ Str.toList "green is a nice colour, isn't it?"
