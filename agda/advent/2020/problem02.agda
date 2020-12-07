module problem02 where

open import Category.Monad

open import Data.Bool.Base
open import Data.Bool.Properties using (T?)
open import Data.Char using (Char; _≟_)
open import Data.List.Base as List using (List; _∷_; []; length; filter)
open import Data.List.NonEmpty using (toList)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Show
open import Data.Product as Prod using (_,_)
open import Data.Product.Nary.NonDependent using (uncurryₙ)
open import Data.String as String using (String; lines)
open import Data.Sum.Base using ([_,_]′)
open import Function.Base

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality.Decidable

record Policy : Set where
  constructor MkPolicy
  field min    : ℕ
        max    : ℕ
        letter : Char

check₁ : Policy → List Char → Bool
check₁ pol cs =
  let open Policy pol in
  let n = length (filter (letter ≟_) cs) in
  (min ≤ᵇ n) ∧ (n ≤ᵇ max)

check₂ : Policy → List Char → Bool
check₂ pol cs = checkIndex (pred min) cs xor checkIndex (pred max) cs where

  open Policy pol

  checkIndex : ℕ → List Char → Bool
  checkIndex 0 (c ∷ _) = does (c ≟ letter)
  checkIndex (suc n) (_ ∷ cs) = checkIndex n cs
  checkIndex _ _ = false

module _ where

  open import Level using (0ℓ)
  open import Text.Parser 0ℓ
  open import Level.Bounded as Level≤ using ([_]; _×_; List; ⊤; ⊥; lift; lower)

  policy : ∀[ Parser [ Policy ] ]
  policy = uncurryₙ 3 MkPolicy
             <$> (decimalℕ
             <&> box ((char '-' &> box decimalℕ)
             <&> box (spaces &> box anyTok)))

  problem : ∀[ Parser ( [ Policy ] × Level≤.List [ Char ]) ]
  problem = policy
        <&> box (toList <$> ((char ':' <&> box spaces)
                         &> box (list⁺ alpha)))

  parse = [ const nothing , just ]′ ∘′ runParser problem

open import IO
open import lib

main = run $ do
  content ← String.lines <$> getInput
  let table = List.mapMaybe parse content
  putStrLn $ show $ length (filter (T? ∘ uncurryₙ 2 check₁) table)
  putStrLn $ show $ length (filter (T? ∘ uncurryₙ 2 check₂) table)
