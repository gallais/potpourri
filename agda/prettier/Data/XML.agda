module Data.XML where

open import Size
open import Data.String
open import Data.List
open import Function

data Attribute : Set where
  Att : String → String → Attribute

-- Termination is typically not obvious when dealing
-- with rose trees. Using a sized type, it is possible
-- to map a recursive call over a whole List of substructures
-- without the system complaining. It's extremely useful!
data XML : {i : Size} → Set where
  Elt : ∀ {i} → String → List Attribute → List (XML {i}) → XML {↑ i}
  Txt : ∀ {i} → String → XML {i}

example : XML
example =
  Elt "p" (Att "color" "red" ∷ Att "font" "Times" ∷ Att "size" "10" ∷ [])
  $ Txt "Here is some"
  ∷ Elt "em" [] [ Txt "emphasized" ]
  ∷ Txt "text."
  ∷ Txt "Here is a "
  ∷ Elt "a" (Att "href" "http://www.eg.com/" ∷ []) (Txt "link" ∷ [])
  ∷ Txt "elsewhere."
  ∷ []
