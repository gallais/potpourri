module lib where

import Data.Char as Char
open import Data.List.Base as List using (List; []; _∷_; [_]; reverse)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Data.String.Base as String using (String)
open import Function.Base

open import IO
open import System.Environment

getInput : IO String
getInput = do
  args ← getArgs
  (just fp) ← pure (List.head args)
    where _ → pure ""
  readFiniteFile fp

open import Data.Bool.Base using (true; false)
open import Relation.Nullary using (does)
open import Relation.Unary using (Pred; Decidable)

-- not yet merged into stdlib
linesBy : ∀ {a} {A : Set a} {p} {P : Pred A p} →
          Decidable P → List A → List (List A)
linesBy {A = A} P? = go nothing where

  go : Maybe (List A) → List A → List (List A)
  go acc []       = maybe′ ([_] ∘′ reverse) [] acc
  go acc (c ∷ cs) with does (P? c)
  ... | true  = reverse (Maybe.fromMaybe [] acc) ∷ go nothing cs
  ... | false = go (just (c ∷ Maybe.fromMaybe [] acc)) cs

lines : String → List String
lines = List.map String.fromList
      ∘ linesBy ('\n' Char.≟_)
      ∘ String.toList
