{-# OPTIONS --without-K --sized-types --safe #-}

module TRANS where

open import Size
open import Codata.Thunk
open import Codata.Stream

variable
  A B : Set
  i : Size

data Trans (A B : Set) (i : Size) : Set where
  put : B → Thunk (Trans A B) i → Trans A B i
  get : (A → Trans A B i) → Trans A B i

trans : Trans A B i → Stream A _ → Stream B i
trans (put b tr) as = b ∷ λ where .force → trans (tr .force) as
trans (get tr)   as = trans (tr (head as)) (tail as)
