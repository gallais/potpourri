module Syntax where

open import Level
open import Data.Char
open import Data.Maybe
open import Data.Unit
open import Data.Product
open import Data.List
open import Function

record RawPartialIso {ℓ : Level} (A B : Set ℓ) : Set ℓ where
  constructor ⟨_∣_⟩
  field
    AtoB : A → Maybe B
    BtoA : B → Maybe A
open RawPartialIso public

flipIso : {ℓ : Level} {A B : Set ℓ} → RawPartialIso A B → RawPartialIso B A
flipIso rpi = ⟨ BtoA rpi ∣ AtoB rpi ⟩

record RawIsoFunctor {ℓ : Level} (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  infix 5 _⟨$⟩_
  field
    _⟨$⟩_ : {A B : Set ℓ} (rpi : RawPartialIso A B) (fa : F A) → F B

record RawProductFunctor {ℓ : Level} (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  infixl 7 _⟨✶⟩_
  field
    _⟨✶⟩_ : {A B : Set ℓ} (fa : F A) (fb : F B) → F (A × B)

record RawAlternative {ℓ : Level} (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  infixl 3 _⟨|⟩_
  field
    _⟨|⟩_ : {A : Set ℓ} (l r : F A) → F A
    ⟨∅⟩ : {A : Set ℓ} → F A

record RawSyntax {ℓ : Level} (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  field
    pure    : {A : Set ℓ} → A → F A
    token   : F (Lift Char)
    rawIso  : RawIsoFunctor F
    rawProd : RawProductFunctor F
    rawAlt  : RawAlternative F
  open RawIsoFunctor rawIso public
  open RawProductFunctor rawProd public
  open RawAlternative rawAlt public

nil : {ℓ : Level} {A : Set ℓ} → RawPartialIso (Lift ⊤) (List A)
nil = ⟨ const (just []) ∣ foldr (λ _ _ → nothing) (just (lift tt)) ⟩

cons : {ℓ : Level} {A : Set ℓ} → RawPartialIso (A × List A) (List A)
cons = ⟨ just ∘′ uncurry _∷_ ∣ (λ { [] → nothing ; (x ∷ xs) → just (x , xs) }) ⟩

many : {ℓ : Level} {F : Set ℓ → Set ℓ} {A : Set ℓ} (rs : RawSyntax F) → F A → F (List A)
many rs fa =
      nil  ⟨$⟩ pure (lift tt)
  ⟨|⟩ cons ⟨$⟩ fa ⟨✶⟩ many rs fa
  where open RawSyntax rs
