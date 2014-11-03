{-# OPTIONS --no-positivity-check #-}
module NonRegParDesc where

open import Data.Unit
open import Data.Product
open import Data.Bool
open import Function

data ParDesc : Set₁ where
  `ret : ParDesc
  `rec : (d e : ParDesc) → ParDesc
  `arg : (A : Set) (d : A → ParDesc) → ParDesc
  `par : (e : ParDesc) → ParDesc

⟦_⟧ : (d : ParDesc) (X : Set → Set) (P : Set) → Set
⟦ `ret     ⟧ X P = ⊤
⟦ `rec d e ⟧ X P = X (⟦ d ⟧ id P) × ⟦ e ⟧ X P
⟦ `arg A d ⟧ X P = Σ[ a ∈ A ] ⟦ d a ⟧ X P
⟦ `par d   ⟧ X P = P × ⟦ d ⟧ X P

data `μ (d : ParDesc) (P : Set) : Set where
  ⟨_⟩ : ⟦ d ⟧ (`μ d) P → `μ d P

Nlist : Set → Set
Nlist = `μ $ `arg Bool $ λ isNil →
             if isNil then `ret
             else `par (`rec (`par $ `par `ret) `ret)

nil : {A : Set} → Nlist A
nil = ⟨ true , tt ⟩

cons : {A : Set} (a : A) → Nlist (A × A × ⊤) → Nlist A
cons a as = ⟨ false , a , as , tt ⟩

example : Nlist Bool
example = cons true $ cons (false , true , tt) nil
