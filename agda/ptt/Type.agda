module ptt.Type where

open import Data.Nat

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
