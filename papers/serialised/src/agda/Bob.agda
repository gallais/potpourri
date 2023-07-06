{-# OPTIONS --guardedness --erasure #-}

module Bob where

open import Data.Default
open import Data.List.Base using ([]; _∷_)
open import Data.Singleton using (getSingleton)
open import Data.String.Base using (_++_)

open import IO.Base
open import IO.Finite

open import System.Environment
open import System.Exit

open import Data.Serialisable.Data
open import Data.Serialisable.Desc hiding (_>>=_)
open import Data.Serialisable.Pointer as Pointer

open import System.Console.ANSI


main : Main
main = run do
  putStrLn (withCommand (setWeight bold) "Hello I am Bob, written in Agda!")

  -- Get the filename in which to read the tree
  (fp₁ ∷ fp₂ ∷ _) ← getArgs
    where _ → die "Expected two file names as an argument."

  -- Read the tree from the file
  _ , ptr ← initFromFile Tree.Tree fp₁
  let tree = deserialise ptr

  putStrLn ("I just read the following tree from file " ++ fp₁ ++ ":")
  putStrLn (Tree.showi "  " (getSingleton tree))

  writeToFile fp₂ (Pointer.Tree.leftBranch ptr)
  putStrLn ("I just serialised the tree's left branch into file " ++ fp₂ ++ ".")
