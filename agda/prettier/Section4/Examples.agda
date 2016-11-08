module Section4.Examples where

open import Data.String
open import Data.String.Extra
open import Data.List
open import Function

open import Data.XML
open import Section4.Core
open Press press

showFill : {A : Set} → (A → List Doc) → List A → Doc
showFill f [] = ε
showFill f xs = bracket "" (fill (concat (map f xs))) ""

showAttributes : Attribute → List Doc
showAttributes (Att n v) = [ text n <> text "=" <> text (quoted v) ]

showTag : String → List Attribute → Doc
showTag n as = text n <> showFill showAttributes as

showXMLs : ∀ {i} → XML {i} → List Doc
showXMLs (Elt n as []) = [ text "<" <> showTag n as <> text "/>" ]
showXMLs (Elt n as xs) = [ text "<" <> showTag n as <> text ">"
                        <> showFill showXMLs xs
                        <> text "</" <> text n <> text ">" ]
showXMLs (Txt s)       = map text $ words s

showXML : XML → Doc
showXML = foldDoc _<>_ ∘ showXMLs

open import Relation.Binary.PropositionalEquality

_ : layout 30 (showXML example)
  ≡ "<p
\   \  color=\"red\" font=\"Times\"
\   \  size=\"10\"
\   \>
\   \  Here is some
\   \  <em> emphasized </em> text.
\   \  Here is a 
\   \  <a
\   \    href=\"http://www.eg.com/\"
\   \  > link </a>
\   \  elsewhere.\n</p>"
_ = refl

_ : layout 60 (showXML example)
  ≡ "<p color=\"red\" font=\"Times\" size=\"10\" >
\   \  Here is some <em> emphasized </em> text. Here is a 
\   \  <a href=\"http://www.eg.com/\" > link </a> elsewhere.
\   \</p>"
_ = refl
