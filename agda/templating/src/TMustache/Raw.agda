module TMustache.Raw where

open import Level using (0ℓ)
open import Data.Bool.Base using (Bool; true; false; not; T)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.List.Base using (List; _∷_; [])
open import Data.List.NonEmpty as List⁺ using (_∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ)
open import Agda.Builtin.String using () renaming (primStringEquality to _≡ᵇ_)
open import Data.String.Base as String using (String; _++_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (⊤)

open import Function.Base using (id; _on_; _$_; _∘′_; case_of_)
import Induction.Nat.Strong as □

Mustache : Set

data Block : Set where
  tag      : (tag : String) → Block
  if_then_ : (tag : String) → Mustache → Block
  forEach  : (tag : String) → Mustache → Block
  literal  : String → Block

Mustache = List Block

open import Text.Parser

iden : ∀[ Parser String ]
iden = String.fromList⁺ <$> alphas⁺

private
  module Mustache {n} (block : Parser Block n) where

    default : Parser Mustache n
    default = List⁺.toList <$> list⁺ block

closing : String → ∀[ Parser ⊤ ]
closing str = _ <$ exacts ('{' ∷ String.toList ("{/" ++ str ++ "}}") )

string : ∀[ Parser String ]
string = String.fromList⁺ <$> alts
  ( (list⁺ (noneOf ('\\' ∷ '{' ∷ [])))
  ∷ (char '\\' &> box (alts $ ((_∷ []) <$> (anyOf ('{' ∷ '\\' ∷ [])))
                            ∷ ((λ c → '\\' ∷ c ∷ []) <$> anyChar)
                            ∷ []))
  ∷ [])

block : ∀[ Parser Block ]
block = fix (Parser Block) $ λ ih →
  let □mustache = □.map Mustache.default ih in
  alts
  $ (tag <$> (text "{{" &> box iden <& box (text "}}")))
  ∷ ((text "{{#" &> box iden) >>= λ str →
     box $ (if str then_) <$> (text "}}" &> □mustache <& box (closing str)))
  ∷ (((text "{{*" &> box iden) >>= λ str →
     box $ (forEach str) <$> (text "}}" &> □mustache <& box (closing str))))
  ∷ (literal ∘′ String.concat ∘′ List⁺.toList <$> list⁺ string)
  ∷ []

mustache : String → Maybe Mustache
mustache str = case runParser (Mustache.default block) str of λ where
  (inj₁ _) → nothing
  (inj₂ mst) → just mst
