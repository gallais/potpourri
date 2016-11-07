module Section2.Examples where

open import Data.Nat
open import Data.Tree
open import Data.List
open import Data.String
open import Function
open import Section2.Core

module ShowTree {ℓ} {Doc : Set ℓ} (p : Press Doc) where

  open Press p

  showTree    : Tree             → Doc
  showTrees   : Tree → List Tree → Doc
  showBracket : List Tree        → Doc 

  showTree (Node s ts) =
    text s <> nest (length (toList s)) (showBracket ts)

  showBracket []       = ε
  showBracket (t ∷ ts) = group $ text "[" <> nest 1 (showTrees t ts) <> text "]"

  showTrees t []        = showTree t
  showTrees t (t′ ∷ ts) = showTree t <> text "," <> line <> showTrees t′ ts


module ShowTree′ {ℓ} {Doc : Set ℓ} (p : Press Doc) where

  open Press p

  showTree    : Tree             → Doc
  showTrees   : Tree → List Tree → Doc
  showBracket : List Tree        → Doc 

  showTree (Node s ts) = text s <> showBracket ts

  showBracket []       = ε
  showBracket (t ∷ ts) = group $ text "[" <> nest 2 (line <> showTrees t ts) <> line <> text "]"

  showTrees t []        = showTree t
  showTrees t (t′ ∷ ts) = showTree t <> text "," <> line <> showTrees t′ ts


pretty : ∀ {ℓ Doc} → (Press {ℓ} Doc → Tree → Doc) → Press Doc → ℕ → Tree → String
pretty show p n t = let open Press p in layout n (show p t)

open import Relation.Binary.PropositionalEquality

-- NB: spaces between two backslashes are ignored in string literals

_ : pretty ShowTree.showTree press 30 example
   ≡ "aaa[bbbbb[ccc, dd],
\    \    eee,
\    \    ffff[gg, hhh, ii]]"
_ = refl

_ : pretty ShowTree′.showTree press 30 example
    ≡ "aaa[
\     \  bbbbb[ ccc, dd ],
\     \  eee,
\     \  ffff[ gg, hhh, ii ]
\     \]"
_ = refl
