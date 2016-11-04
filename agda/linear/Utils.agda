module linear.Utils where

open import Level
open import Data.List
open import Data.Vec
open import Relation.Binary.PropositionalEquality

toList∘fromList : {ℓ : Level} {A : Set ℓ} (xs : List A) → toList (fromList xs) ≡ xs
toList∘fromList []       = refl
toList∘fromList (x ∷ xs) = cong (x ∷_) (toList∘fromList xs)

