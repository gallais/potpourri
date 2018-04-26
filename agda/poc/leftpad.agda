module leftpad where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Vec
open import Data.Product

data LeOrGt : ℕ → ℕ → Set where
  le : ∀ m k → LeOrGt m (k + m)
  gt : ∀ m k → LeOrGt (suc k + m) m

compare : ∀ m n → LeOrGt m n
compare = {!!}


_⊔_ : ℕ → ℕ → ℕ
m ⊔ n with compare m n
... | le _ _ = n
... | gt _ _ = m

module _ {a} {A : Set a} (x : A) where

  data LeftPad {n : ℕ} (xs : Vec A n) : ∀ m → Vec A m → Set where
    Padded : ∀ k → LeftPad xs (k + n) (replicate {n = k} x ++ xs)

  leftPad : ∀ n m (xs : Vec A n) → ∃ (LeftPad xs (n ⊔ m))
  leftPad n m xs with compare n m
  ... | le .n k = , Padded k
  ... | gt .m k = , Padded 0
