{-
   This algorithm is taken from Danvy and Millikin's
   Refactorisation at Work (2007)
   https://ojs.statsbiblioteket.dk/index.php/brics/article/view/21930
-}

module poc.InfixParser where

open import Data.Nat
open import Data.Maybe as Maybe
open import Data.Product
open import Data.List
open import Relation.Nullary
open import Category.Monad
open import Function

record Ope (O : Set) : Set where
  constructor _at_
  field operator : O
        fixity   : ℕ
open Ope

module _ (L O : Set) where

  data Token : Set where
    LIT   : L     → Token
    OPE   : Ope O → Token
    LP RP : Token

  Tokens = List Token

  data Expr : Set where
    LIT : L → Expr
    OPE : O → Expr → Expr → Expr

pattern [PAR]   = nothing
pattern [OPE] x = just x

module _ {L O : Set} where

  parse : List (Token L O) → Maybe (Expr L O)
  parse = go [] [] where

    pop[PAR] : List (Maybe (Ope O)) → List (Expr L O) → Maybe (List (Maybe (Ope O)) × List (Expr L O))
    pop[PAR] ([PAR]   ∷ os) es             = just (os , es)
    pop[PAR] ([OPE] o ∷ os) (e₁ ∷ e₂ ∷ es) = pop[PAR] os (OPE (operator o) e₂ e₁ ∷ es)
    pop[PAR] _ _ = nothing

    open RawMonad Maybe.monad

    go : List (Maybe (Ope O)) → List (Expr L O) → List (Token L O) → Maybe (Expr L O)
    -- finishing up
    go []             (e ∷ [])       [] = just e
    go ([OPE] o ∷ os) (e₁ ∷ e₂ ∷ es) [] = go os (OPE (operator o) e₂ e₁ ∷ es) []
    -- base case
    go os es (LIT l ∷ ts) = go os (LIT l ∷ es) ts
    -- parentheses
    go os es (LP ∷ ts) = go ([PAR] ∷ os) es ts
    go os es (RP ∷ ts) = pop[PAR] os es >>= λ where (os , es) → go os es ts
    -- operator
    go []                  es       (OPE o ∷ ts) = go ([OPE] o ∷ []) es ts
    go os@([PAR]    ∷ _)   es       (OPE o ∷ ts) = go ([OPE] o ∷ os) es ts
    go os@([OPE] o′ ∷ os′) es       (OPE o ∷ ts) = case suc (fixity o′) ≤? fixity o of λ
      { (yes p) → go ([OPE] o ∷ os) es ts
      ; (no ¬p) → case es of λ
                   { (e₁ ∷ e₂ ∷ es) → go ([OPE] o ∷ os′) (OPE (operator o′) e₂ e₁ ∷ es) ts
                   ; _ → nothing } }
    go _ _ _ = nothing


private

  module Example where

    open import Data.String
    open import Relation.Binary.PropositionalEquality

    PLUS : Ope String
    PLUS = "plus" at 1

    MULT : Ope String
    MULT = "mult" at 2

    ADD : Token ℕ String
    ADD = OPE PLUS

    MUL : Token ℕ String
    MUL = OPE MULT

    tokens : Tokens ℕ String
    tokens = LIT 10 ∷ MUL ∷ LIT 20 ∷ ADD ∷ LIT 30 ∷ MUL ∷ LP ∷ LIT 40 ∷ ADD ∷ LIT 50 ∷ RP ∷ []

    expr : Expr ℕ String
    expr = OPE "plus" (OPE "mult" (LIT 10) (LIT 20)) (OPE "mult" (LIT 30) (OPE "plus" (LIT 40) (LIT 50))) 

    test : parse tokens ≡ just expr
    test = refl
