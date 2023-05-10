{-# OPTIONS --erasure --guardedness #-}

module Main where

open import Data.Buffer
open import Data.Buffer.IO
open import Data.Serialisable.Data; open Tree
open import Data.Serialisable.Pointer

open import Data.Default
import Data.Nat.Show as ℕ
open import Data.String.Base
open import Function.Base using (_$_)

open import IO

main : Main
main = run $ do
  putStrLn "Loading from file tmp"
  _ , ptr ← initFromFile Tree "tmp"
  putStrLn "Successfully loaded file"
  putStrLn ("Sum: " ++ ℕ.show (Tree.sum ptr))
