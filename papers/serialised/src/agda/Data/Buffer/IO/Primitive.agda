module Data.Buffer.IO.Primitive where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)
open import IO.Primitive using (IO)

open import Data.Buffer.Primitive

postulate
  readFile : String → IO Buffer
  writeFile : String → Buffer → IO ⊤

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import Data.ByteString #-}
{-# COMPILE GHC readFile = Data.ByteString.readFile . T.unpack #-}
{-# COMPILE GHC writeFile = Data.ByteString.writeFile . T.unpack #-}
