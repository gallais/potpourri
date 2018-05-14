module ListSpec where

open import Level
open import Data.Unit
open import Data.Product
open import Data.Nat as Nat hiding (_⊔_)
open import Function

ListAlg : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
ListAlg A B = B × (A → B → B)

data ListSpec {a b} (A : Set a) {B : Set b} (alg : ListAlg A B) : B → Set (a ⊔ b) where
  nil  :  ListSpec A alg (proj₁ alg)
  cons : (a : A) {b : B} (as : ListSpec A alg b) → ListSpec A alg (proj₂ alg a b)

-- USUAL LISTS
------------------------------------------------------------------------------

-- For usual lists our algebra is the most boring possible: the invariant
-- we compute is the unit type.

AlgList : ∀ {a} (A : Set a) → ListAlg A ⊤
AlgList A = tt , λ _ _ → tt

List : ∀ {a} → Set a → Set a
List A = ListSpec A (AlgList A) tt

-- example: a list of Sets

Sets : List Set
Sets = cons ⊤ (cons ℕ (cons Level (cons (ℕ × ℕ) nil)))

-- HETEROGENEOUS LISTS
------------------------------------------------------------------------------

-- For heterogeneous lists we collect the list of Sets the terms stored in
-- the list belong to.

AlgSet : ListAlg (Σ[ A ∈ Set ] A) (List Set)
AlgSet = nil
       , uncurry λ A a As → cons A As

HList : List Set → Set₁
HList = ListSpec _ AlgSet

-- Example: values for each one of the sets stored in the `Sets` example
-- defined earlier

UnitNat^2 : HList Sets
UnitNat^2 = cons (, tt)
          $ cons (, 3)
          $ cons (, Level.zero)
          $ cons (, 5 , 1) nil

-- INCREASING LISTS
------------------------------------------------------------------------------

open import Data.Maybe
open import Data.Bool
open import Relation.Nullary.Decidable

AlgIncr : ListAlg ℕ (Maybe ℕ × Bool)
AlgIncr = (nothing , true)
        , λ p → uncurry λ mq b →
          just p , maybe (⌊_⌋ ∘ (p Nat.≤?_)) true mq ∧ b

SList : Set
SList = ∃ (ListSpec _ AlgIncr ∘ (_, true))

1⋯3 : SList
1⋯3 = , cons 1 (cons 2 (cons 3 nil))

-- Invalid test case:

-- ¬3⋯1 : SList
-- ¬3⋯1 = , cons 3 (cons 2 (cons 1 nil))

-- false != true of type Bool
-- when checking that the expression cons 3 (cons 2 (cons 1 nil)) has
-- type ((λ {.x} → ListSpec ℕ AlgIncr) ∘ (_, true)) (just 3)
