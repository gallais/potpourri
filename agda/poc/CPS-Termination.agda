module poc.CPS-Termination where

open import Data.Nat
open import Data.List
open import Function
open import Relation.Binary.PropositionalEquality

data Tree {ℓ} (A : Set ℓ) : Set ℓ where
  Leaf : A → Tree A
  Node : Tree A → Tree A → Tree A

example : Tree ℕ
example =
  Node (Node (Leaf 0) (Leaf 1))
       (Node (Leaf 2) (Leaf 3))

module StackBased where

  -- Here we use a stack of subtrees that will have to be
  -- traversed to collect the leaves in the remaining subtrees.
  -- Naturally, Agda does not see that the recursive calls are
  -- all strictly smaller.
  {-# TERMINATING #-}
  flatten : ∀ {ℓ} {A : Set ℓ} → Tree A → List A
  flatten = go [] where

    go : ∀ {ℓ} {A : Set ℓ} → List (Tree A) → Tree A → List A
    go ts       (Node t₁ t₂) = go (t₂ ∷ ts) t₁
    go []       (Leaf a)     = a ∷ []
    go (t ∷ ts) (Leaf a)     = a ∷ go ts t

  _ : flatten example ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
  _ = refl

module CPSBased where

  flatten : ∀ {ℓ} {A : Set ℓ} → Tree A → List A
  flatten t = go t [] where

    go : ∀ {ℓ} {A : Set ℓ} → Tree A → List A → List A
    go (Leaf a)     = a ∷_
    go (Node t₁ t₂) = go t₁ ∘ go t₂

  _ : flatten example ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
  _ = refl
