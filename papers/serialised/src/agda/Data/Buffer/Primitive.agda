module Data.Buffer.Primitive where

open import Agda.Builtin.Nat
open import Data.Word8.Primitive
open import Data.Int64.Primitive

postulate
  Buffer : Set
  index : Buffer → Int64 → Word8
  length : Buffer → Nat
  take : Int64 → Buffer → Buffer
  drop : Int64 → Buffer → Buffer

{-# FOREIGN GHC import qualified Data.ByteString as B #-}
{-# COMPILE GHC Buffer = type B.ByteString #-}
{-# COMPILE GHC index = \ buf idx -> B.index buf (fromIntegral idx) #-}
{-# COMPILE GHC length = \ buf -> fromIntegral (B.length buf) #-}
{-# COMPILE GHC take = B.take . fromIntegral #-}
{-# COMPILE GHC drop = B.drop . fromIntegral #-}
