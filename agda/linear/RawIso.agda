module linear.RawIso where

open import Function
open import Data.Product
open import Relation.Nullary

record RawIso (A B : Set) : Set where
  constructor mkRawIso
  field
    push : A → B
    pull : B → A
open RawIso public

infixl 2 _<$>_
_<$>_ : {A B : Set} (f : RawIso A B) → Dec A → Dec B
f <$> yes p = yes (push f p)
f <$> no ¬p = no (¬p ∘ pull f)

infixr 3 _<*>_
_<*>_ : {A B : Set} → Dec A → Dec B → Dec (A × B)
yes a <*> yes b = yes (a , b)
no ¬a <*> b     = no (¬a ∘ proj₁)
a     <*> no ¬b = no (¬b ∘ proj₂)
