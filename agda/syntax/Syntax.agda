module Syntax where

open import Level
open import Data.Char
open import Data.Maybe as Maybe
open import Data.Unit
open import Data.Product as Prod
open import Data.List as List
open import Coinduction
open import Function
open import Delay
open import Category.Monad
module M {ℓ : Level} = RawMonad {ℓ} Maybe.monad

record RawPartialIso {ℓ : Level} (A B : Set ℓ) : Set ℓ where
  constructor ⟨_∣_⟩
  field
    push : A → Maybe B
    pull : B → Maybe A
open RawPartialIso public

flipIso : {ℓ : Level} {A B : Set ℓ} → RawPartialIso A B → RawPartialIso B A
flipIso rpi = ⟨ pull rpi ∣ push rpi ⟩

infix  5 _⟨$⟩_
infixl 7 _⟨✶⟩_
infixl 3 _⟨|⟩_
data Syntax {ℓ : Level} : (A : Set ℓ) → Set (suc ℓ) where
  pure  : {A : Set ℓ} → A → Syntax A
  token : Syntax (Lift Char)
  -- _⟨$⟩_ behaves a bit like a constructor.
  -- Indeed the RawPartialIso shaves constructors off / adds them
  _⟨$⟩_ : {A B : Set ℓ} (rpi : RawPartialIso A B) (f : ∞ (Syntax A)) → Syntax B
  _⟨✶⟩_ : {A B : Set ℓ} (fa : Syntax A) (fb : Syntax B) → Syntax (A × B)
  _⟨|⟩_ : {A : Set ℓ} (la ra : Syntax A) → Syntax A
  ⟨⊘⟩   : {A : Set ℓ} → Syntax A

ParserT : {ℓ : Level} (M : Set ℓ → Set ℓ) (A : Set ℓ) → Set ℓ
ParserT M A = List Char → M (Maybe (A × List Char))

PrinterT : {ℓ : Level} (M : Set ℓ → Set ℓ) (A : Set ℓ) → Set ℓ
PrinterT M A = A → M (Maybe (Lift $ List Char))

toMaybe : {ℓ : Level} {A : Set ℓ} (xs : List A) → Maybe (A × List A)
toMaybe []       = nothing
toMaybe (x ∷ xs) = just (x , xs)

nil : {ℓ : Level} {A : Set ℓ} → RawPartialIso (Lift ⊤) (List A)
nil = ⟨ const (just []) ∣ foldr (λ _ _ → nothing) (just (lift tt)) ⟩

cons : {ℓ : Level} {A : Set ℓ} → RawPartialIso (A × List A) (List A)
cons = ⟨ just ∘′ uncurry _∷_ ∣ (λ { [] → nothing ; (x ∷ xs) → just (x , xs) }) ⟩

many : {ℓ : Level} {A : Set ℓ} → Syntax A → Syntax (List A)
many fa =
      nil  ⟨$⟩ ♯ pure (lift tt)
  ⟨|⟩ cons ⟨$⟩ ♯ (fa ⟨✶⟩ many fa)
