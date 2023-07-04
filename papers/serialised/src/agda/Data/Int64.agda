module Data.Int64 where

open import Agda.Builtin.FromNat; open Number ⦃...⦄ public
open import Agda.Builtin.Unit using (⊤)

------------------------------------------------------------------------------
-- Re-exporting definitions

open import Data.Int64.Primitive as Prim public
  using ( Int64
        ; show
        ; _+_
        ; _-_
        )
  renaming ( fromNat to fromℕ
           ; toNat to toℕ
           ; _==_ to _≡ᵇ_
           )

------------------------------------------------------------------------------
-- Syntactic sugar for literals

instance
  fromNatInt64 : Number Int64
  fromNatInt64 .Constraint n = ⊤
  fromNatInt64 .fromNat n = Prim.fromNat n
