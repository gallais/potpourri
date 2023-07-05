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
open import Data.Serialisable.Pointer

open import System.Console.ANSI


main : Main
main = run do
  putStrLn (withCommand (setWeight bold) "Hello I am Agda!")

  -- Get the filename in which to read the tree
  (fp ∷ _) ← getArgs
    where [] → die "Expected a file name as an argument"

  -- Read the tree from the file
  _ , tree ← initFromFile Tree.Tree fp
  let tree = deserialise tree

  putStrLn ("I just read the following tree from file " ++ fp ++ ":")
  putStrLn (Tree.show (getSingleton tree))
