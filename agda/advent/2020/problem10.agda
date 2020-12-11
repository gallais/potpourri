module problem10 where

open import Data.List.Base as List using (List; _∷_; [])
open import Data.Maybe.Base using (fromMaybe)
open import Data.Nat.Base using (ℕ; suc; _∸_; _*_)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String.Base using (lines)
open import Function.Base

import Data.Tree.AVL.Sets ℕₚ.<-strictTotalOrder as Sets
open import Data.Tree.AVL.Map ℕₚ.<-strictTotalOrder as Map using (Map)

record Differentials : Set where
  field one : ℕ
        three : ℕ

differentials : List ℕ → Differentials
differentials [] = record { one = 0; three = 0 }
differentials (n ∷ ns) =
  let (_ , m) = List.foldl step (n , Map.empty) ns in
  record { one = fromMaybe 0 (Map.lookup 1 m)
         ; three = fromMaybe 0 (Map.lookup 3 m)
         }
  where

    step : ℕ × Map ℕ → ℕ → ℕ × Map ℕ
    step (old , m) new = new , Map.insertWith (new ∸ old) (suc ∘′ fromMaybe 0) m

open import lib
open import IO

main = run $ do
  lines ← lines <$> getInput
  let ns = List.mapMaybe readMaybe lines
  let sorted = 0 ∷ let open Sets in toList (fromList ns)
  let diffs = differentials sorted
  let open Differentials diffs
  putStrLn $ show $ one
  putStrLn $ show $ suc three
  putStrLn $ show $ one * suc three
