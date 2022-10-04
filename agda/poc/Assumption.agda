module Assumption where

open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product
open import Level
open import Data.Unit.Base
open import Function.Base
open import Reflection

private
  variable
    a b : Level
    A : Set a
    B : Set b

first : (A → Maybe B) → List A → Maybe (ℕ × B)
first f = go 0 where

  go : ℕ → List A → Maybe (ℕ × B)
  go _ [] = nothing
  go idx (a ∷ as) = case f a of
    just b → just (idx , b)
    nothing → go (suc idx) as

macro
  assumption : Term → TC ⊤
  assumption hole = do
    goal ← inferType hole
    asss ← getContext
    {!!}
    {!!}
