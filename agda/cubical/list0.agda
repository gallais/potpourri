{-# OPTIONS --cubical #-}

module list0 where

open import Cubical.Core.Prelude

data List⁰ (A : Set) : Set where
  []  : List⁰ A
  _∷_ : A → List⁰ A → List⁰ A
  del : ∀ x y → x ∷ y ≡ y

variable A : Set

_≡[] : (e : List⁰ A) → e ≡ []
([]        ≡[]) j = []
((x ∷ e)   ≡[]) j = del x ((e ≡[]) j) j
(del x e i ≡[]) j = del x ((e ≡[]) j) (i ∨ j)

_++_ : (e f : List⁰ A) → List⁰ A
[]        ++ f = f
(x ∷ e)   ++ f = x ∷ (e ++ f)
del x y i ++ f = del x (y ++ f) i
  -- s.t   i = 0 -> (x ∷ y) ++ f = x ∷ (y ++ f)
  --       i = 1 ->                     y ++ f

dels : (e f : List⁰ A) → e ++ f ≡ f
dels []          f j = f
dels (x ∷ e)     f j = del x (dels e f j) j
dels (del x e i) f j = del x (dels e f j) (i ∨ j)
