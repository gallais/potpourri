module Data.String.Extra where

open import Data.Bool
open import Data.Product
open import Data.List as List
open import Data.Char as Char
open import Data.String as String
open import Function
open import Relation.Binary.PropositionalEquality

breaks : ∀ {ℓ} {A : Set ℓ} (P : A → Bool) → List A → List (List A)
breaks {_} {A} P = uncurry _∷_ ∘ foldr cons ([] , []) where

  cons : A → List A × List (List A) → List A × List (List A)
  cons a (xs , xss) = if P a then ([] , xs ∷ xss)
                             else (a ∷ xs , xss)

words : String → List String
words = List.map fromList ∘ breaks (Char._==_ ' ') ∘ toList

_ : words "Hello world, This a test! And it works!"
  ≡ "Hello" ∷ "world," ∷ "This" ∷ "a" ∷ "test!" ∷ "And" ∷ "it" ∷ "works!" ∷ []
_ = refl

quoted : String → String
quoted v = "\"" String.++ v String.++ "\""
