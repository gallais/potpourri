module poc.MixfixParser where

open import Data.Nat.Base
open import Data.Vec

data Fixity (O : Set) : ℕ → Set where
  Prefix : ∀ {n} → O → Vec O n → Fixity O (suc n)
  Infix  : ∀ {n} → O → Vec O n → Fixity O (suc n)
  Suffix : ∀ {n} → Vec O n → O → Fixity O (n + 1)
  Closed : ∀ {n} → O → Vec O n → O → Fixity O (suc n + 1)

record Operator (O : Set) : Set where
  constructor _at_
  field {pieces} : ℕ
        fixity   : Fixity O pieces
        level    : ℕ
open Operator

data Tree (O : Set) : Set where
  Node : (o : Operator O) → Vec (Tree O) (pieces o) → Tree O

data PartialTree (O : Set) : Set where
  [PAR] : PartialTree O
  [OPE] : (o : Operator O)
          {n : ℕ} → n <′ pieces o → (Vec (Tree O) n → Tree O) →
          PartialTree O

data Token (O : Set) : Set where
  Tok   : O → Token O
  LP RP : Token O

open import Data.Maybe
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Relation.Binary

module _ {O} {{eq? : Decidable {A = O} _≡_}} where

  parse : List (PartialTree O) → List (Token O) → Maybe (Tree O)
  parse = {!!}
