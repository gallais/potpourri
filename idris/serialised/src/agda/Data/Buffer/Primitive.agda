module Data.Buffer.Primitive where

open import Agda.Builtin.Nat
open import Agda.Builtin.String using (String)
open import Data.Word8.Primitive
open import IO.Primitive using (IO)

postulate
  Buffer : Set
  index : Buffer → Nat → Word8
  readFile : String → IO Buffer

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import Data.ByteString #-}
{-# COMPILE GHC Buffer = type ByteString #-}
{-# COMPILE GHC index = \ buf idx -> Data.ByteString.index buf (fromIntegral idx) #-}
{-# COMPILE GHC readFile = \ fp -> Data.ByteString.readFile (T.unpack fp) #-}
