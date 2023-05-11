module Data.Word8 where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.FromNat; open Number ⦃...⦄ public
open import Agda.Builtin.Nat using (Nat; _==_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)

------------------------------------------------------------------------------
-- Re-export type and operations

open import Data.Word8.Primitive as Prim public
  using ( Word8
        ; _+_)
  renaming (toNat to toℕ)

------------------------------------------------------------------------------
-- Syntactic sugar for literals

instance
  fromNatWord8 : Number Word8
  fromNatWord8 .Constraint n = ⊤
  fromNatWord8 .fromNat n = Prim.fromNat n

------------------------------------------------------------------------------
-- Basic functions

_≡ᵇ_ : Word8 → Word8 → Bool
w ≡ᵇ w′ = toℕ w == toℕ w′
