module poc.LinearDec where

open import Data.Empty
open import Data.Maybe.Base
open import Data.Nat.Base
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

data _∼_ : (m n : ℕ) → Set where
  zero :         zero  ∼ zero
  suc  : ∀ m n → suc m ∼ suc n

view : ∀ m n → Maybe (m ∼ n)
view zero    zero    = just zero
view (suc m) (suc n) = just (suc m n)
view _ _ = nothing

view-diag : ∀ m → ¬ (view m m ≡ nothing)
view-diag zero    ()
view-diag (suc m) ()

_≟_ : (m n : ℕ) → Dec (m ≡ n)
m ≟ n with view m n | inspect (view m) n
._ ≟ ._ | just zero      | eq     = yes refl
._ ≟ ._ | just (suc m n) | eq     = map′ (cong suc) (λ where refl → refl) (m ≟ n)
(m ≟ n) | nothing        | [ eq ] = no λ where refl → view-diag _ eq

≟-diag : ∀ m → m ≟ m ≡ yes refl
≟-diag m with view m m | inspect (view m) m
≟-diag ._ | just zero       | eq                      = refl
≟-diag ._ | just (suc m .m) | eq     rewrite ≟-diag m = refl
≟-diag m  | nothing         | [ eq ] = ⊥-elim (view-diag _ eq)
