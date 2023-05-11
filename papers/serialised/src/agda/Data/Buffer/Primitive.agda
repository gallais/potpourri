module Data.Buffer.Primitive where

open import Agda.Builtin.Nat
open import Data.Word8.Primitive

postulate
  Buffer : Set
  index : Buffer → Nat → Word8
  length : Buffer → Nat

{-# FOREIGN GHC import Data.ByteString #-}
{-# COMPILE GHC Buffer = type ByteString #-}
{-# COMPILE GHC index = \ buf idx -> Data.ByteString.index buf (fromIntegral idx) #-}
{-# COMPILE GHC length = \ buf -> fromIntegral (Data.ByteString.length buf) #-}
