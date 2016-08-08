module monoid.Normalise where

open import Level
open import Data.Nat
open import Data.Fin
open import Data.List
open import Algebra
open import Function

open import monoid.Utils
open import monoid.Monoid

module Semantics {ℓ^A ℓ^E} (m : Monoid ℓ^A ℓ^E) where

  module Mon = Monoid m
  open Mon

  M : ℕ → Set _
  M = λ _ → Carrier

  ⟦_⟧_ : Expr ⟶ Values M ⟶′ M
  ⟦ var k   ⟧ ρ = lookup ρ k
  ⟦ one     ⟧ ρ = ε
  ⟦ bin e f ⟧ ρ = ⟦ e ⟧ ρ ∙ ⟦ f ⟧ ρ

  mconcat : List Carrier → Carrier
  mconcat = foldr _∙_ ε

Model : (n : ℕ) → Set
Model n = List (Fin n)

eval : Expr ⟶ Model
eval (var k)   = k ∷ []
eval one       = []
eval (bin e f) = eval e ++ eval f

reify : Model ⟶ Expr
reify []       = one
reify (x ∷ []) = var x
reify (x ∷ xs) = bin (var x) (reify xs)

norm : Expr ⟶ Expr
norm = reify ∘ eval

DModel : (n : ℕ) → Set
DModel n = Model n → Model n

deval : Expr ⟶ DModel
deval (var k)   = k ∷_
deval one       = id
deval (bin e f) = deval e ∘ deval f

dreify : DModel ⟶ Expr
dreify = reify ∘ (_$ [])

dnorm : Expr ⟶ Expr
dnorm = dreify ∘ deval
