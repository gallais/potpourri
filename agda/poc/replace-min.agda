module poc.replace-min where

open import Data.Nat.Base
open import Data.Product
open import Function.Base

data Tree : Set where
  leaf : ℕ → Tree
  node : Tree → Tree → Tree

{-# TERMINATING #-}
relabel : Tree → Tree
relabel t = tree where

  mutual

    done = repmin t
    tree = proj₁ done
    min  = proj₂ done

    repmin : Tree → Tree × ℕ
    repmin (leaf n)   = leaf min , n
    repmin (node l r) =
      let (l′ , ml) = repmin l
          (r′ , mr) = repmin r
      in node l′ r′ , ml ⊓ mr

repmin-cps : Tree → (ℕ → Tree) × ℕ
repmin-cps (leaf n)   = leaf , n
repmin-cps (node l r) =
   let (l′ , ml) = repmin-cps l
       (r′ , mr) = repmin-cps r
   in (λ n → node (l′ n) (r′ n)) , ml ⊓ mr

relabel′ : Tree → Tree
relabel′ = uncurry _$_ ∘ repmin-cps

