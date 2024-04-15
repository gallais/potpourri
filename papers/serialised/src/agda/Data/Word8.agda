module Data.Word8 where

open import Data.Bool.Base using (Bool; T)
open import Agda.Builtin.FromNat; open Number ⦃...⦄ public
open import Data.Nat.Base as ℕ using (ℕ; _≤ᵇ_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)
open import Data.Product.Base using (Σ-syntax; _,_)

------------------------------------------------------------------------------
-- Re-export type and operations

open import Data.Word8.Primitive as Prim public
  using ( Word8
        ; _+_)
  renaming ( fromNat to fromℕ
           ; toNat to toℕ
           )

-- Unfortunately we have to postulate this constraint because
-- Word8 is postulated and so there is no way to prove it manually.
word8AsBoundedNat : (i : Word8) → Σ[ n ∈ ℕ ] (T (n ≤ᵇ 255))
word8AsBoundedNat i = toℕ i , trustMe where postulate trustMe : _

------------------------------------------------------------------------------
-- Syntactic sugar for literals

instance
  fromNatWord8 : Number Word8
  fromNatWord8 .Constraint n = ⊤
  fromNatWord8 .fromNat n = Prim.fromNat n

------------------------------------------------------------------------------
-- Basic functions

_≡ᵇ_ : Word8 → Word8 → Bool
w ≡ᵇ w′ = toℕ w ℕ.≡ᵇ toℕ w′
