{-# OPTIONS -v1 #-}

module poc.Assumption where

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base as M using (Maybe; just; nothing)
open import Data.Nat.Base
open import Level using (Level)
open import Data.Unit.Base
open import Function.Base
open import Reflection as R hiding (_>>=_; _≟_)
open import Reflection.AST.DeBruijn
open import Reflection.AST.Term
open import Relation.Nullary

private
  variable
    a b : Level
    A : Set a
    B : Set b

-- As the doc states (cf. https://agda.readthedocs.io/en/latest/language/reflection.html#type-checking-computations)
-- Note that the types in the context are valid in the rest of the context.
-- To use in the current context they need to be weakened by 1 + their position
-- in the list.

-- That is to say that the type of the current goal needs to be strengthened
-- before being compared to the type of the most local variable. The goal
-- indeed lives below that variable's binding site!

searchEntry : ℕ → Type → List Type → Maybe ℕ
searchEntry n ty [] = nothing
searchEntry n ty (e ∷ es) = let open M in do
  ty ← strengthen ty
  if does (ty ≟ e)
    then just n
    else searchEntry (suc n) ty es

unArg : Arg A → A
unArg (arg _ a) = a

macro
  assumption : Term → TC ⊤
  assumption hole = let open R in do
    asss ← getContext
    goal ← inferType hole
    debugPrint "" 10
      (strErr "Context : "
       ∷ concatMap (λ where (arg info ty) → strErr "\n  " ∷ termErr ty ∷ []) asss)
    let res = searchEntry 0 goal (map unArg asss)
    case res of λ where
      nothing → typeError (strErr "Couldn't find an assumption of type: " ∷ termErr goal ∷ [])
      (just idx) → unify hole (var idx [])

test₀ : A → B → B
test₀ x y = assumption

test₁ : A → B → A
test₁ x y = assumption

test₂ : A → B → B → A
test₂ x y z = assumption

test₃ : List (A → B) → A → B → B → List (A → B)
test₃ x y z a = assumption

test₄ : (A → List B) → A → B → List B → A → List B
test₄ x y z a = assumption
