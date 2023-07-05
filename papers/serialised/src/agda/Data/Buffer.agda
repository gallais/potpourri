module Data.Buffer where

open import Data.Nat.Base using (ℕ; _+_; _*_; _^_)
open import Agda.Builtin.String using (String)
import Data.Fin.Base as Fin
open import Data.Int64 as Int64 using (Int64; _-_)
import Data.Vec.Base as Vec
open import Data.Word8 as Word8 using (Word8)
open import Data.Word.Base as Word64 using (Word64)

open import Function.Base using (const; _$_)

------------------------------------------------------------------------------
-- Re-export type and operations

open import Data.Buffer.Primitive as Prim public
  using ( Buffer
        ; length
        ; take
        ; drop
        )
  renaming (index to getWord8)

------------------------------------------------------------------------------
-- Operations

slice : Int64 → Int64 → Buffer → Buffer
slice start chunk buf = take chunk (drop start buf)

getWordN : (n : ℕ) → Buffer → Int64 → ℕ
getWordN n buf idx
  = Vec.foldr (const ℕ) (λ w i → i * (2 ^ 8) + Word8.toℕ w) 0
  $ Vec.map (λ k → getWord8 buf (idx Int64.+ Int64.fromℕ (Fin.toℕ k)))
  $ Vec.allFin n

getWord64 : Buffer → Int64 → Word64
getWord64 buf idx = Word64.fromℕ (getWordN 8 buf idx)

getInt64 : Buffer → Int64 → Int64
getInt64 buf idx = Int64.fromℕ (getWordN 8 buf idx)
