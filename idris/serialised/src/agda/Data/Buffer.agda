{-# OPTIONS --guardedness #-}

module Data.Buffer where

open import Data.Nat.Base using (ℕ; _+_; _*_; _^_)
open import Agda.Builtin.String using (String)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
open import Data.Word8 as Word8 using (Word8)
open import Data.Word.Base as Word64 using (Word64)
open import IO.Base using (IO; lift)

open import Function.Base using (const; _$_)

------------------------------------------------------------------------------
-- Re-export type and operations

open import Data.Buffer.Primitive as Prim
  using ( Buffer
        ) public

------------------------------------------------------------------------------
-- Operations

readFile : String → IO Buffer
readFile fp = lift (Prim.readFile fp)

getWord8 : Buffer → ℕ → Word8
getWord8 = Prim.index

getWordN : (n : ℕ) → Buffer → ℕ → ℕ
getWordN n buf idx
  = Vec.foldr (const ℕ) (λ w i → i * (2 ^ 8) + Word8.toℕ w) 0
  $ Vec.map (λ k → getWord8 buf (idx + Fin.toℕ k))
  $ Vec.allFin n

getWord64 : Buffer → ℕ → Word64
getWord64 buf idx = Word64.fromℕ (getWordN 8 buf idx)
