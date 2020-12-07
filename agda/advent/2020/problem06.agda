module problem06 where

open import Data.Bool.Properties using (T?)
open import Data.Char.Base using (Char)
import Data.Char.Properties as Charₚ
open import Data.List.Base as List using (List)
import Data.List.NonEmpty as List⁺
open import Data.Maybe.Base as Maybe using (maybe′)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String as String using (String)
open import Function.Base

open import lib

split : String → List (List String)
split = List.wordsBy ("" String.≟_) ∘′ lines

open import Data.Tree.AVL.Sets Charₚ.<-strictTotalOrder-≈ as Sets

any : List (List Char) → ℕ
any = List.length
    ∘′ Sets.toList
    ∘′ Sets.fromList
    ∘′ List.concat

all : List (List Char) → ℕ
all = List.length
   ∘′ Sets.toList
   ∘′ maybe′ (List⁺.foldr intersect Sets.fromList) Sets.empty
   ∘′ List⁺.fromList

  where

    intersect : List Char → ⟨Set⟩ → ⟨Set⟩
    intersect cs set = Sets.fromList
                     $ List.filter (T? ∘ (_∈? set)) cs

open import IO

main = run $ do
  content ← getInput
  let answers = List.map (List.map String.toList) (split content)
--  List.mapM′ (putStrLn ∘′ show) sizes
  putStrLn $ show $ List.sum (List.map any answers)
  putStrLn $ show $ List.sum (List.map all answers)
