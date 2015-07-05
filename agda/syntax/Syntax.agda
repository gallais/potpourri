{-# OPTIONS --copatterns #-}

module Syntax where

open import Level
open import Size
open import Data.Char
open import Data.Maybe as Maybe
open import Data.Unit
open import Data.Product as Prod
open import Data.List as List
open import Function
open import Delay as Delay
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

mutual

  data Syntax (i : Size) {ℓ : Level} : (A : Set ℓ) → Set (suc ℓ) where
    pure  : {A : Set ℓ} → A → Syntax i A
    token : Syntax i (Lift Char)
    -- _⟨$⟩_ behaves a bit like a constructor.
    -- Indeed the RawPartialIso shaves constructors off / adds them
    _⟨$⟩_ : {A B : Set ℓ} (rpi : RawPartialIso A B) (f : ∞Syntax i A) → Syntax i B
    _⟨✶⟩_ : {A B : Set ℓ} (fa : Syntax i A) (fb : Syntax i B) → Syntax i (A × B)
    _⟨|⟩_ : {A : Set ℓ} (la ra : Syntax i A) → Syntax i A
    ⟨⊘⟩   : {A : Set ℓ} → Syntax i A

  record ∞Syntax (i : Size) {ℓ : Level} (A : Set ℓ) : Set (suc ℓ) where
    coinductive
    constructor ⟨_⟩
    field
      force : {j : Size< i} → Syntax i A
open ∞Syntax

ParserT : {ℓ ℓ′ : Level} (M : Set ℓ → Set ℓ′) (A : Set ℓ) → Set ℓ′
ParserT M A = List Char → M (Maybe (A × List Char))

failParse : {i : Size} {ℓ : Level} {A : Set ℓ} → Delay i (Maybe (A × List Char))
failParse = now nothing

resultBind :
  {i : Size} {ℓ : Level} {A B : Set ℓ} (dm : Delay i (Maybe (A × List Char)))
  (f : A → List Char → Delay i (Maybe (B × List Char))) →
  Delay i (Maybe (B × List Char))
resultBind d f = Delay.bind d $ maybe′ (uncurry f) failParse

mutual

  parser : {i : Size} {ℓ : Level} {A : Set ℓ} (s : Syntax i A) → ParserT (Delay i) A
  parser (pure x)    xs       = now $ just (x , xs)
  parser token       []       = failParse
  parser token       (x ∷ xs) = now $ just $ lift x , xs
  parser (rpi ⟨$⟩ s) xs       = later (Delay.∞map f′ (∞parser s xs))
    where f′ = flip (M._>>=_) $ uncurry $ λ a ys → Maybe.map (λ b → b , ys) $ push rpi a
  parser (s₁ ⟨✶⟩ s₂) xs       = resultBind (parser s₁ xs) $ λ a ys →
                                resultBind (parser s₂ ys) $ λ b zs →
                                now $ just $ (a , b) , zs
  parser (s₁ ⟨|⟩ s₂) xs       = Delay.bind (parser s₁ xs) $ maybe′ (now ∘ just) (parser s₂ xs)
  parser ⟨⊘⟩         xs       = failParse

  ∞parser : {i : Size} {ℓ : Level} {A : Set ℓ} (s : ∞Syntax i A) → ParserT (∞Delay i) A
  ∞Delay.force (∞parser s xs) {j} = parser (∞Syntax.force s {j}) xs

PrinterT : {ℓ : Level} (M : Set ℓ → Set ℓ) (A : Set ℓ) → Set ℓ
PrinterT M A = A → M (Maybe (Lift $ List Char))

toMaybe : {ℓ : Level} {A : Set ℓ} (xs : List A) → Maybe (A × List A)
toMaybe []       = nothing
toMaybe (x ∷ xs) = just (x , xs)

nil : {ℓ : Level} {A : Set ℓ} → RawPartialIso (Lift ⊤) (List A)
nil = ⟨ const (just []) ∣ foldr (λ _ _ → nothing) (just (lift tt)) ⟩

cons : {ℓ : Level} {A : Set ℓ} → RawPartialIso (A × List A) (List A)
cons = ⟨ just ∘′ uncurry _∷_ ∣ (λ { [] → nothing ; (x ∷ xs) → just (x , xs) }) ⟩


mutual

  many : {i : Size} {ℓ : Level} {A : Set ℓ} → Syntax i A → Syntax i (List A)
  many a =
          cons ⟨$⟩ manyCons a
      ⟨|⟩ nil  ⟨$⟩ ⟨ pure (lift tt) ⟩

  manyCons : {i : Size} {ℓ : Level} {A : Set ℓ} → Syntax i A → ∞Syntax i (A × List A)
  ∞Syntax.force (manyCons a) = a ⟨✶⟩ many a

open import Data.Nat
open import Data.Sum
open import Data.String
open import Data.Nat.Show as Nat
open import Data.Nat.Read

nat : {i : Size} → Syntax i ℕ
nat = ⟨ ([ const nothing , just ]′ ∘ parseℕ ∘ fromList ∘ List.map lower)
      ∣ just ∘′ List.map lift ∘′ toList ∘′ Nat.show
      ⟩ ⟨$⟩ ⟨ many token ⟩

open import Relation.Binary.PropositionalEquality

test :
  let result = proj₁ $ from-just $ from-just
             $ runDelay 10 $ parser nat $ toList $ "914"
  in result ≡ 914
test = refl
