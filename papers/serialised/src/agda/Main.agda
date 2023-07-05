{-# OPTIONS --erasure --guardedness #-}

module Main where

open import Data.Buffer
open import Data.Buffer.IO
open import Data.Serialisable.Data as Data; open Tree
open import Data.Serialisable.Pointer as Pointer

open import Data.Default
open import Data.List.Base using (_∷_; [])
open import Data.Maybe.Base using (Maybe; nothing; just)
import Data.Nat.Show as ℕ
open import Data.Singleton using (getSingleton)
open import Data.String.Base
open import Data.Word8 as Word8

open import Function.Base using (_$_; _∘_)

open import IO

header : String → String
header str = unlines ("" ∷ replicate 72 '-' ∷ ("-- " ++ str) ∷ "" ∷ [])


fromFile : String → IO _
fromFile fp = do
  putStrLn $ header ("File " ++ fp)
  _ , ptr ← initFromFile Tree fp
  let t = getSingleton $ deserialise ptr
  putStrLn ("Tree:\n" ++ Tree.showi "  " t)
  putStrLn ("Sum (pure / pointer): "
            ++ ℕ.show (Data.Tree.sum t)
            ++ " / "
            ++ ℕ.show (getSingleton (Pointer.Tree.sum ptr)))
  putStrLn ("Right (pure / pointer): "
            ++ mshow (ℕ.show ∘ Word8.toℕ) (Data.Tree.right t)
            ++ " / "
            ++ mshow (ℕ.show ∘ Word8.toℕ) (getSingleton (Pointer.Tree.right ptr)))

  let fp = fp ++ "-left"
  writeToFile fp (Pointer.Tree.leftBranch ptr)
  _ , ptr ← initFromFile Tree fp
  putStrLn ("Left branch (pure / pointer):\n"
           ++ Tree.showi "  " (leftBranch t)
           ++ "\n"
           ++ Tree.showi "  " (getSingleton $ deserialise ptr))

  where

    mshow : ∀ {a} {A : Set a} (s : A → String) → Maybe A → String
    mshow s nothing = "nothing"
    mshow s (just v) = "just " ++ s v

main : Main
main = run $ do
  fromFile "tmp"
  fromFile "tmp2"
  fromFile "tmp3"
