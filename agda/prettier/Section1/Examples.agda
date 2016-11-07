module Section1.Examples where

open import Data.Tree
open import Data.List
open import Data.String
open import Section1.Core

module ShowTree {ℓ} {Doc : Set ℓ} (p : Press Doc) where

  open Press p

  showTree    : Tree             → Doc
  showTrees   : Tree → List Tree → Doc
  showBracket : List Tree        → Doc 

  showTree (Node s ts) =
    text s <> nest (length (toList s)) (showBracket ts)

  showBracket []       = ε
  showBracket (t ∷ ts) = text "[" <> nest 1 (showTrees t ts) <> text "]"

  showTrees t []        = showTree t
  showTrees t (t′ ∷ ts) = showTree t <> text "," <> line <> showTrees t′ ts


module ShowTree′ {ℓ} {Doc : Set ℓ} (p : Press Doc) where

  open Press p

  showTree    : Tree             → Doc
  showTrees   : Tree → List Tree → Doc
  showBracket : List Tree        → Doc 

  showTree (Node s ts) = text s <> showBracket ts

  showBracket []       = ε
  showBracket (t ∷ ts) = text "[" <> nest 2 (line <> showTrees t ts) <> line <> text "]"

  showTrees t []        = showTree t
  showTrees t (t′ ∷ ts) = showTree t <> text "," <> line <> showTrees t′ ts

pretty : ∀ {ℓ Doc} → (Press {ℓ} Doc → Tree → Doc) → Press Doc → Tree → String
pretty show p t = let open Press p in layout (show p t)


open import Relation.Binary.PropositionalEquality

-- NB: spaces between two backslashes are ignored in string literals

_ : pretty ShowTree.showTree press example
   ≡ "aaa[bbbbb[ccc,
\    \          dd],
\    \    eee,
\    \    ffff[gg,
\    \         hhh,
\    \         ii]]"
_ = refl

_ : pretty ShowTree′.showTree press example
    ≡ "aaa[
\     \  bbbbb[
\     \    ccc,
\     \    dd
\     \  ],
\     \  eee,
\     \  ffff[
\     \    gg,
\     \    hhh,
\     \    ii
\     \  ]
\     \]"
_ = refl
