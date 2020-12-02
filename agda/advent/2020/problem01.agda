module problem01 where

open import Category.Monad
open import Data.Bool.Base
open import Data.Char.Base
open import Data.List.Base as List
import Data.List.Categorical as List
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Nat.Base
import Data.Nat.Properties as ℕₚ
import Data.Nat.Show as ℕ
open import Data.Product
open import Data.String.Base as String
open import Data.Tree.AVL.Sets ℕₚ.<-strictTotalOrder as Sets using (⟨Set⟩)
open import Data.Unit.Base

open import Function.Base

candidate₂ : List ℕ → Maybe (ℕ × ℕ)
candidate₂ = go Sets.empty where

  go : ⟨Set⟩ → List ℕ → Maybe (ℕ × ℕ)
  go seen [] = nothing
  go seen (n ∷ ns) =
    let nᶜ = 2020 ∸ n in
    if (n ≤ᵇ 2020) ∧ (nᶜ Sets.∈? seen)
    then just (n , nᶜ)
    else go (Sets.insert n seen) ns

candidate₃ : List ℕ → Maybe (ℕ × ℕ × ℕ)
candidate₃ ns = let open RawMonad List.monad in head $ do
  (p , qs) ← pick ns
  (q , rs) ← pick qs
  guard (p + q ≤ᵇ 2020)
  r ← rs
  guard (p + q + r ≡ᵇ 2020)
  pure (p , q , r)

  where
    guard : Bool → List ⊤
    guard b = if b then _ ∷ [] else []

    pick : List ℕ → List (ℕ × List ℕ)
    pick [] = []
    pick (n ∷ ns) = (n , ns) ∷ pick ns

read : String → ℕ
read = foldl (λ acc c → 10 * acc + char c) 0 ∘′ toList where

  char : Char → ℕ
  char c = toℕ c ∸ toℕ '0'

open import IO
open import System.Environment

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
  case candidate₂ numbers of λ where
    nothing → putStrLn "No candidate₂"
    (just (m , n)) → putStrLn $ ℕ.show (m * n)
  case candidate₃ numbers of λ where
    nothing → putStrLn "No candidate₃"
    (just (m , n , p)) → putStrLn $ ℕ.show (m * n * p)
