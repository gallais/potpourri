{-# OPTIONS --erasure --guardedness #-}

module Data.Serialisable.Tree where

open import Agda.Builtin.FromNat using (fromNat)
open import Agda.Builtin.FromString using (fromString)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty.Base using (List⁺; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just; _<∣>_)
open import Data.Nat.Base using (ℕ; suc; _+_)
import Data.Nat.Show as ℕ
open import Data.Product.Base using (_,_)
open import Data.Singleton using (Singleton; pure; _<*>_)
open import Data.String.Base as String using (String; unlines; unwords)
open import Data.String.Literals; instance StringIsString = isString
open import Data.Unit.Base using (⊤)
open import Data.Vec.Base using ([]; _∷_)
open import Data.Word8 as Word8 using (Word8)

open import Function.Base using (_$′_)

open import Data.Serialisable.Desc hiding (module Data; pure)
open import Data.Serialisable.Data
open import Data.Serialisable.Pointer

------------------------------------------------------------------------
-- Definition of the datatype: data Tree = Leaf | Node Tree Word8 Tree
-- and pattern synonyms

Leaf Node : Constructor String

Leaf = "leaf" ∶ none
Node = "node" ∶ prod rec (prod byte rec)

Tree : Data String
Tree = mkData (Leaf ∷ Node ∷ [])

module Patterns where

  open import Data.Fin.Base using (zero; suc)
  pattern leaf = mkIndex zero
  pattern node = mkIndex (suc zero)

------------------------------------------------------------------------
-- Smart constructors and examples

leaf : μ Tree
leaf = "leaf" , _

node : μ Tree → Word8 → μ Tree → μ Tree
node l b r = "node" , l , b , r

example : μ Tree
example =
  (node
    (node (node leaf 1 leaf) 5 leaf)
    10
    (node leaf 20 leaf))

bigexample : μ Tree
bigexample =
  (node
    (node (node leaf 1 leaf) 5 leaf)
    10
    (node leaf 20
      (node
        (node leaf 56 (node leaf 5 leaf))
        17
        (node leaf 23
          (node leaf 78 leaf)))))

------------------------------------------------------------------------
-- Fancy show function

showi : String → μ Tree → String
showi pad t = unlines (let (hd ∷ tl) = go 0 pad t [] in (pad String.++ hd) ∷ tl) where

  open Patterns

  go : ℕ → String → μ Tree → List String → List⁺ String
  go closings pad (leaf , _) = ("leaf" String.++ String.replicate closings ')') ∷_
  go closings pad (node , (leaf , _) , b , (leaf , _))
    = let byte = ℕ.show (Word8.toℕ b) in
      (unwords ("(node" ∷ "leaf" ∷ byte ∷ "leaf" ∷ []) String.++ String.replicate (suc closings) ')') ∷_
  go closings pad (node , l , b , r) acc
    = let pad = "      " String.++ pad in
      let hd₁ ∷ tl₁ = go (suc closings) pad r acc in
      let byte = pad String.++ ℕ.show (Word8.toℕ b) in
      let hd₂ ∷ tl₂ = go 0 pad l $′ byte ∷ (pad String.++ hd₁) ∷ tl₁ in
      ("(node " String.++ hd₂) ∷ tl₂

show : μ Tree → String
show = showi ""

------------------------------------------------------------------------
-- Pure versions of the functions

module Data where

  open Patterns

  sum : μ Tree → ℕ
  sum (leaf , _) = 0
  sum (node , l , b , r)
    = let m = sum l
          n = sum r
      in m + Word8.toℕ b + n

  rightmost : μ Tree → Maybe Word8
  rightmost (leaf , _) = nothing
  rightmost (node , l , b , r)
    = rightmost r <∣> just b

  leftBranch : μ Tree → μ Tree
  leftBranch t@(leaf , _) = t
  leftBranch (node , l , _ , _) = l

------------------------------------------------------------------------
-- Correct-by-construction functions working on buffer-bound data

module Pointer where

  open Patterns

  sum : ∀ {@0 t} → μ Tree ∋ t → Singleton (Data.sum t)
  sum t with view t
  ... | leaf , _ = ⦇ 0 ⦈
  ... | node , l , b , r
    = let m = sum l
          n = sum r
      in ⦇ ⦇ m + ⦇ Word8.toℕ b ⦈ ⦈ + n ⦈

  rightmost : ∀ {@0 t} → μ Tree ∋ t → Singleton (Data.rightmost t)
  rightmost t with view t
  ... | leaf , _ = ⦇ nothing ⦈
  ... | node , l , b , r = ⦇ rightmost r <∣> ⦇ just b ⦈ ⦈

  leftBranch : ∀ {@0 t} → μ Tree ∋ t → μ Tree ∋ Data.leftBranch t
  leftBranch t with view t
  ... | leaf , _ = t
  ... | node , l , _ , _ = l
