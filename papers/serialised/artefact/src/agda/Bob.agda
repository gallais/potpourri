{-# OPTIONS --guardedness --erasure #-}

module Bob where

open import Data.Default
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (nothing; just)
import Data.Nat.Show as ℕ
open import Data.Singleton using (getSingleton)
open import Data.String.Base using (_++_)
import Data.Word8 as Word8

open import IO.Base
open import IO.Finite

open import Function.Base using (_$′_; case_of_)

open import System.Environment
open import System.Exit

open import Data.Serialisable.Data
open import Data.Serialisable.Desc hiding (_>>=_)
open import Data.Serialisable.Pointer as Pointer
open import Data.Serialisable.Tree

open import System.Console.ANSI


main : Main
main = run do
  putStrLn (withCommand (setWeight bold) "Hello I am Bob, written in Agda!")

  -- Get the filename in which to read the tree
  (fp₁ ∷ fp₂ ∷ _) ← getArgs
    where _ → die "Expected two file names as an argument."

  -- Read the tree from the file
  _ , ptr ← initFromFile Tree fp₁
  let tree = deserialise ptr

  putStrLn ("I just read the following tree from file " ++ fp₁ ++ ":")
  putStrLn (showi "  " (getSingleton tree))

  case getSingleton $′ Pointer.rightmost ptr of λ where
    nothing  → putStrLn "It does not have a rightmost node. :("
    (just w) → putStrLn ("Its rightmost node's value is: " ++ ℕ.show (Word8.toℕ w) ++ ".")

  writeToFile fp₂ (Pointer.leftBranch ptr)
  putStrLn ("I just serialised the tree's left branch into file " ++ fp₂ ++ ".")
