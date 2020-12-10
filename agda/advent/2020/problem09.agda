module problem09 where

open import Level using (Level)
open import Category.Monad

open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base as List using (List; []; _∷_)
import Data.List.Categorical as List
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; _≡ᵇ_; _≤ᵇ_; _+_; _∸_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String.Base as String using (String)
open import Function.Base

private
  variable
    a : Level
    A : Set a

allSplits : List A → List (A × List A)
allSplits = List.mapMaybe List.uncons ∘ List.tails

findMatch : ℕ → List ℕ → List (ℕ × ℕ)
findMatch n ns = let open RawMonad List.monad in do
  (k , tl) ← allSplits ns
  (l , _)  ← allSplits tl
  if k + l ≡ᵇ n then (k , l) ∷ [] else []

search : List ℕ → List ℕ → Maybe ℕ
search ns []       = nothing
search ns (n ∷ tl) = case findMatch n ns of λ where
  [] → just n
  _ → let window = n ∷ Maybe.maybe′ proj₁ [] (List.unsnoc ns)
      in search window tl

findPrefix : ℕ → List ℕ → Maybe (List ℕ)
findPrefix 0 _ = just []
findPrefix _ [] = nothing
findPrefix n (hd ∷ tl) =
  if hd ≤ᵇ n then Maybe.map (hd ∷_) (findPrefix (n ∸ hd) tl) else nothing

open import IO
open import lib
open import Data.List.Extrema.Nat

main = run $ do
  lines ← String.lines <$> getInput
  let nats = List.mapMaybe readMaybe lines
  let (pref , rest) = List.splitAt 25 nats
  case search (List.reverse pref) rest of λ where
    nothing → putStrLn "No error!"
    (just n) → do
      putStrLn $ show n
      case List.mapMaybe (findPrefix n) (List.tails nats) of λ where
        ((hd ∷ seg) ∷ _) → do
          let small = min hd seg
          let big   = max hd seg
          putStrLn $ show $ small + big
        _ → putStrLn "No segment!"
