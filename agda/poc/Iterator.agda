module poc.Iterator where

open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Nat.Primality
open import Data.Bool
open import Relation.Nullary.Decidable hiding (map)
open import Data.Product hiding (map)
open import Data.List as List using (List)
open import Function
open import Data.Char
open import Data.String as String using (String)
open import Data.Maybe as Maybe using (Maybe)

record Iterator (A : Set) : Set₁ where
  coinductive
  field
    map     : ∀ {B} → (A → B) → Iterator B
    mapi    : ∀ {B} → (A → ℕ → B) → Iterator B
    filter  : (A → Bool) → Iterator A
    collect : List A
open Iterator

fromList : {A : Set} → List A → Iterator A
map     (fromList xs) f = fromList (List.map f xs)
mapi    (fromList xs) f = fromList (List.zipWith f xs (List.scanl (const ∘ suc) 0 xs))
filter  (fromList xs) p = fromList (List.filter p xs)
collect (fromList xs)   = xs

fromString : String → Iterator Char
fromString = fromList ∘ String.toList

fromMaybe : {A : Set} → Maybe A → Iterator A
fromMaybe = fromList ∘ Maybe.maybe List.[_] List.[]

odds : Iterator ℕ → List ℕ
odds v = v .map (λ n → n , ⌊ 2 ∣? n ⌋)
           .filter (not ∘ proj₂)
           .map proj₁
           .collect

primes-up-to : ℕ → List (ℕ × ℕ) -- [(n, nth prime)]
primes-up-to n = fromList (List.replicate n 0)
               .mapi (λ _ → id)
               .filter (λ n → ⌊ prime? n ⌋)
               .mapi (flip _,_)
               .collect
