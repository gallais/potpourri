module Data.Tree where

open import Data.List
open import Data.String
open import Function

data Tree : Set where
  Node : String → List Tree → Tree

example : Tree
example = Node "aaa"
        $ Node "bbbbb" (Node "ccc" []
                      ∷ Node "dd"  []
                      ∷ [])
        ∷ Node "eee" []
        ∷ Node "ffff" (Node "gg" []
                     ∷ Node "hhh" []
                     ∷ Node "ii" []
                     ∷ [])
        ∷ []
