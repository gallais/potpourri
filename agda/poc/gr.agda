module poc.gr where

variable
  A : Set
  B : A → Set
  a a′ : A

-- GR is an indexed monad reifying what it means to be able
-- to make arbitrary recursive calls
data GR (A : Set) (B : A → Set) (X : Set) : Set where
  pure : X → GR A B X
  ask  : ∀ a → (B a → GR A B X) → GR A B X

open import IO
open import Codata.Musical.Notation

-- If for any input we can compute a bunch of recursive calls
-- and then an output, then we can compute an IO-function making
-- these recursive calls as needed
runGR : (∀ a → GR A B (B a)) → ∀ a → IO (B a)
runGR {A = A} {B = B} f a = go (f a) where

  go : ∀ {a} → GR A B (B a) → IO (B a)
  go (pure b)  = return b
  go (ask q k) = ♯ go (f q) >>= λ r → ♯ go (k r)

open import Data.String.Base using (String; toList; _++_)

-- Because it was pretty boring to just wait for collatz to terminate,
-- here is an instrumented version of runGR that prints the successive
-- values the program uses for its recursive calls
-- ᴵ for Instrumented
runGRᴵ : (A → String) → (∀ a → GR A B (B a)) → ∀ a → IO (B a)
runGRᴵ {A = A} {B = B} toStr f a = go (f a) where

  go : ∀ {a} → GR A B (B a) → IO (B a)
  go (pure b)  = return b
  go (ask q k) =
    ♯ (putStrLn (toStr q)) >> ♯ (♯ go (f q) >>= λ r → ♯ go (k r))

open import Data.Nat.Base
open import Data.Nat.DivMod

-- Collatz sequence

collatzGR : ℕ → GR ℕ (λ _ → ℕ) ℕ
-- stop if you started at 0 / when you reach 1
collatzGR 0 = pure 0
collatzGR 1 = pure 1
-- otherwise perform a recursive call with argument
--   n/2   if n is even
--   3*n+1 otherwise
collatzGR n = ask next pure where

  next : ℕ
  next with n % 2
  ... | zero = n / 2
  ... | _    = suc (3 * n)

collatzIO : ℕ → IO ℕ
collatzIO = runGR collatzGR

open import Data.Nat.Show using (show)

collatzIOᴵ : ℕ → IO ℕ
collatzIOᴵ = runGRᴵ show collatzGR

open import Data.Char.Base
open import Data.Maybe.Base as M using (Maybe; nothing; just)
open import Data.List.Base using (List; []; _∷_; foldl)
open import Function

-- Annoying bits about parsing the argument

readChar : Char → Maybe ℕ
readChar c = case c of λ where
  '0' → just 0
  '1' → just 1
  '2' → just 2
  '3' → just 3
  '4' → just 4
  '5' → just 5
  '6' → just 6
  '7' → just 7
  '8' → just 8
  '9' → just 9
  _ → nothing

readString : String → Maybe ℕ
readString = foldl (λ l → step l ∘ readChar) (just 0) ∘ toList where

  step : Maybe ℕ → Maybe ℕ → Maybe ℕ
  step (just l) (just d) = just (10 * l + d)
  step _ _ = nothing

-- Annoying bits about grabbing an executable's arguments

import IO.Primitive as Prim

postulate primGetArgs : Prim.IO (List String)
{-# FOREIGN GHC import System.Environment           #-}
{-# FOREIGN GHC import Data.Text                    #-}
{-# COMPILE GHC primGetArgs = fmap pack <$> getArgs #-}

getArgs : IO (List String)
getArgs = lift primGetArgs

-- Finally, our main function

open import Data.Unit

callCollatz : List String → IO ⊤
callCollatz (str ∷ []) = case readString str of λ where
  (just c) → ♯ (collatzIOᴵ c) >> ♯ (return _)
  nothing  → putStrLn $ "Invalid input: " ++ str ++ " should be a number"
callCollatz _ =
  putStrLn $ "Invalid argument: expected a single natural number"

main : _
main = run (♯ getArgs >>= λ args → ♯ (callCollatz args))
