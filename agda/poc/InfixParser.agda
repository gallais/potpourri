{-
   This example of Dijkstra's shunting-yard algorithm is taken from
   Danvy and Millikin's Refactorisation at Work (2007)
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

data OPEPAR (O : Set) : Set where
  [PAR] : OPEPAR O
  [OPE] : Ope O → OPEPAR O

module _ {L O : Set} where

  parse : List (Token L O) → Maybe (Expr L O)
  parse = go [] [] where

    -- unrolling the stack of operators looking for an opening parenthesis
    pop[PAR] : List (OPEPAR O) → List (Expr L O) →
               Maybe (List (OPEPAR O) × List (Expr L O))
    pop[PAR] ([PAR]   ∷ os) es             = just (os , es)
    pop[PAR] ([OPE] o ∷ os) (e₁ ∷ e₂ ∷ es) = pop[PAR] os (OPE (operator o) e₂ e₁ ∷ es)
    pop[PAR] _ _ = nothing

    open RawMonad Maybe.monad

    go : List (OPEPAR O) → List (Expr L O) → List (Token L O) → Maybe (Expr L O)
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

  open import Data.String
  open import Relation.Binary.PropositionalEquality

  module Example1 where

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

private

  module Example2 where

    open import Data.Char

    PLUS : Ope Char
    PLUS = '+' at 1

    MULT : Ope Char
    MULT = '*' at 2

    open import Level
    open RawMonad (Maybe.monad {Level.zero})

    tokenise : List Char → Maybe (List (Token ℕ Char))
    tokenise = go nothing where

      isDigit : Char → Maybe ℕ
      isDigit '0' = just 0
      isDigit '1' = just 1
      isDigit '2' = just 2
      isDigit '3' = just 3
      isDigit '4' = just 4
      isDigit '5' = just 5
      isDigit '6' = just 6
      isDigit '7' = just 7
      isDigit '8' = just 8
      isDigit '9' = just 9
      isDigit _   = nothing

      push : Maybe ℕ → Token ℕ Char → List (Token ℕ Char) → List (Token ℕ Char)
      push nothing  t ts = t ∷ ts
      push (just n) t ts = LIT n ∷ t ∷ ts

      go : Maybe ℕ → List Char → Maybe (List (Token ℕ Char))
      go mn []       = just (maybe (λ n → LIT n ∷ []) [] mn)
      go mn (c ∷ cs) = case c of λ
        { '+' → push mn (OPE PLUS) <$> go nothing cs
        ; '*' → push mn (OPE MULT) <$> go nothing cs
        ; '(' → push mn LP         <$> go nothing cs
        ; ')' → push mn RP         <$> go nothing cs
        ; c   → isDigit c >>= λ d → go (maybe (λ n → just (n * 10 + d)) (just d) mn) cs
        }

    tokens : Tokens ℕ Char
    tokens = from-just $ tokenise $ toList "10*20+30*(40+50)"

    expr : Expr ℕ Char
    expr = OPE '+' (OPE '*' (LIT 10) (LIT 20)) (OPE '*' (LIT 30) (OPE '+' (LIT 40) (LIT 50)))

    test : parse tokens ≡ just expr
    test = refl
