module monoid.Monoid where

open import Level
open import Data.Nat
open import Data.Product
open import Data.List hiding (monoid)
open import Data.Fin
open import Algebra
open import Algebra.Structures
open import Algebra.FunctionProperties
open import Function
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning

open import monoid.Utils

data Expr (n : ℕ) : Set where
  var : (k : Fin n) → Expr n
  one : Expr n
  bin : (e f : Expr n) → Expr n

rawInsert : Expr ⟶ Expr ⟶′ Expr
rawInsert (var k)   = bin (var k)
rawInsert one       = id
rawInsert (bin e f) = bin e ∘ rawInsert f

insert : Expr ⟶ Expr ⟶′ Expr
insert e one = e
insert e f   = rawInsert e f

module Syntactic (n : ℕ) where

  isSemigroup : IsSemigroup _≡_ (insert {n})
  isSemigroup = record
              { isEquivalence = isEquivalence
              ; assoc         = assoc
              ; ∙-cong        = cong₂ insert } where

    rawAssoc : Associative _≡_ rawInsert
    rawAssoc (var k)   f g = refl
    rawAssoc one       f g = refl
    rawAssoc (bin t u) f g = cong (bin t) (rawAssoc u f g)

    assoc : Associative _≡_ insert
    assoc e f one = refl
    assoc e (var k) (var l) = rawAssoc e (var k) (var l)
    assoc e one (var k) = refl
    assoc e (bin t u) (var k) = rawAssoc e (bin t u) (var k)
    assoc e (var k) (bin g h) = rawAssoc e (var k) (bin g h)
    assoc e one (bin g h) = refl
    assoc e (bin t u) (bin g h) = rawAssoc e (bin t u) (bin g h)

  isMonoid : IsMonoid _≡_ insert one
  isMonoid = record
           { isSemigroup = isSemigroup
           ; identity = left-identity , (λ _ → refl) } where

    left-identity : LeftIdentity _≡_ one insert
    left-identity (var k)   = refl
    left-identity one       = refl
    left-identity (bin e f) = refl

  monoid : Monoid _ _
  Monoid.Carrier  monoid = Expr n
  Monoid._≈_      monoid = _≡_
  Monoid._∙_      monoid = insert
  Monoid.ε        monoid = one
  Monoid.isMonoid monoid = isMonoid
