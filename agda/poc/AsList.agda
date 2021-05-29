module AsList where

open import Data.Char.Base
open import Function.Base using (_∋_)
open import Data.List.Base using ([_])
open import Data.Maybe.Base using (nothing; just; maybe′)
open import Data.Product using (_,_; uncurry)
open import Data.String.Base
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

cons : Char → String → String
cons c str = fromList [ c ] ++ str

uncons-correct : (str : String) → maybe′ (uncurry cons) "" (uncons str) ≡ str
uncons-correct str = trustMe

data Split : String → Set where
  [] : Split ""
  _∷_ : (c : Char) (str : String) → Split (cons c str)

split : ∀ str → Split str
split str with uncons str | uncons-correct str
... | nothing        | refl = []
... | just (c , str) | refl = c ∷ str

data AsList : String → Set where
  [] : AsList ""
  _∷_ : (c : Char) {str : String} → AsList str → AsList (cons c str)

{-# TERMINATING #-}
asList : ∀ str → AsList str
asList str with split str
... | []      = []
... | c ∷ str = c ∷ asList str
