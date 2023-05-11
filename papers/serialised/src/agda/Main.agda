{-# OPTIONS --erasure --guardedness #-}

module Main where

open import Data.Buffer
open import Data.Buffer.IO
open import Data.Serialisable.Data as Data; open Tree
open import Data.Serialisable.Pointer as Pointer

open import Data.Default
import Data.Nat.Show as ℕ
open import Data.Singleton using (getSingleton)
open import Data.String.Base
open import Function.Base using (_$_)

open import IO

main : Main
main = run $ do
  putStrLn "Loading from file tmp"
  _ , ptr ← initFromFile Tree "tmp"
  putStrLn "Successfully loaded file"
  let t = getSingleton $ deserialise ptr
  putStrLn ("Tree:\n" ++ Tree.showi "  " t)
  putStrLn ("Sum (pure / pointer): "
            ++ ℕ.show (getSingleton (Pointer.Tree.sum ptr))
            ++ " / "
            ++ ℕ.show (Data.Tree.sum t))
