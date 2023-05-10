{-# OPTIONS --guardedness #-}

module Data.Buffer.IO where

open import Agda.Builtin.String
open import IO using (IO; lift)
open import Data.Buffer using (Buffer)
open import Data.Unit.Base using (⊤)

import Data.Buffer.IO.Primitive as Prim

readFile : String → IO Buffer
readFile fp = lift (Prim.readFile fp)

writeFile : String → Buffer → IO ⊤
writeFile fp str = lift (Prim.writeFile fp str)
