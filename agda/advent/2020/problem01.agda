module problem01 where

open import Data.Bool.Base
open import Data.Char.Base
open import Data.List.Base as List
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Nat.Base
import Data.Nat.Properties as ℕₚ
import Data.Nat.Show as ℕ
open import Data.Product
open import Data.String.Base as String
open import Data.Tree.AVL.Sets ℕₚ.<-strictTotalOrder as Sets using (⟨Set⟩)

open import Function.Base
open import IO
open import System.Environment

candidate : List ℕ → Maybe (ℕ × ℕ)
candidate = go Sets.empty where

  go : ⟨Set⟩ → List ℕ → Maybe (ℕ × ℕ)
  go seen [] = nothing
  go seen (n ∷ ns) =
    let nᶜ = 2020 ∸ n in
    if (n ≤ᵇ 2020) ∧ (nᶜ Sets.∈? seen)
    then just (n , nᶜ)
    else go (Sets.insert n seen) ns

read : String → ℕ
read = foldl (λ acc c → 10 * acc + char c) 0 ∘′ toList where

  char : Char → ℕ
  char c = toℕ c ∸ toℕ '0'

getInput : IO String
getInput = do
  args ← getArgs
  pure $ case args of λ where
    (fp ∷ []) → fp
    _ → ""

main = run $ do
  fp ← getInput
  content ← lines <$> readFiniteFile fp
  let numbers = List.map read content
  case candidate numbers of λ where
    nothing → putStrLn "No candidate"
    (just (m , n)) → putStrLn $ ℕ.show (m * n)
