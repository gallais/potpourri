module Data.Buffer.Builder where

------------------------------------------------------------------------------
-- Re-export type and operations

open import Data.Buffer.Builder.Primitive as Prim public
  using ( Builder
        ; toBuffer
        ; buffer
        ; word8
        ; int64LE
        ; empty
        ; _<>_
        )
