module lib where

open import Data.Char as Char using (Char)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.List.Base as List using (List; []; _∷_; [_]; reverse)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Data.Nat.Base using (suc)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String.Base as String using (String)
open import Function.Base

open import IO
open import System.Environment

getInput : IO String
getInput = do
  args ← getArgs
  (just fp) ← pure (List.head args)
    where _ → pure ""
  readFiniteFile fp

open import Data.Bool.Base using (_∧_)
open import Data.Nat.Base as ℕ using (ℕ; _∸_; _+_; _*_)

readMaybe : String → Maybe ℕ
readMaybe = List.foldl step (just 0) ∘′ String.toList where

  digit : Char → Maybe ℕ
  digit c = let check = (Char.toℕ '0' ℕ.≤ᵇ Char.toℕ c)
                      ∧ (Char.toℕ c ℕ.≤ᵇ Char.toℕ '9')
            in Maybe.map (const (Char.toℕ c ∸ Char.toℕ '0'))
                         (Maybe.boolToMaybe check)

  step : Maybe ℕ → Char → Maybe ℕ
  step nothing _ = nothing
  step (just acc) c = Maybe.map (λ c → 10 * acc + c) (digit c)

showℤ : ℤ → String
showℤ (+ n)    = showℕ n
showℤ -[1+ n ] = "-" String.++ showℕ (suc n)
