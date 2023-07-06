module Data.Buffer.Builder.Primitive where

open import Agda.Builtin.Nat
open import Agda.Builtin.String

open import Data.Word8.Primitive
open import Data.Int64.Primitive
open import Data.Buffer.Primitive using (Buffer)

infixr 6 _<>_

postulate
  -- Builder and execution
  Builder : Set
  toBuffer : Builder → Buffer

  -- Assembling a builder
  buffer : Buffer → Builder
  word8 : Word8 → Builder
  int64LE : Int64 → Builder
  empty : Builder
  _<>_ : Builder → Builder → Builder

{-# FOREIGN GHC import qualified Data.ByteString.Builder as Builder #-}
{-# FOREIGN GHC import qualified Data.ByteString.Lazy as Lazy #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC Builder = type Builder.Builder #-}
{-# COMPILE GHC toBuffer = Lazy.toStrict . Builder.toLazyByteString #-}
{-# COMPILE GHC buffer = Builder.byteString #-}
{-# COMPILE GHC word8 = Builder.word8 #-}
{-# COMPILE GHC int64LE = Builder.int64LE #-}
{-# COMPILE GHC empty = mempty #-}
{-# COMPILE GHC _<>_ = mappend #-}
