{-# OPTIONS --copatterns #-}

module Syntax where

open import Level
open import Size
open import Data.Char
open import Data.Maybe as Maybe
open import Data.Unit as Unit
open import Data.Product as Prod
open import Data.List as List
open import Function
open import Delay as Delay
open import Category.Monad
open import lib.Nullary
open import Relation.Nullary
open import Relation.Binary as RBi using (DecSetoid ; module DecSetoid)
open import Relation.Binary.PropositionalEquality as PEq
module M {ℓ : Level} = RawMonad {ℓ} Maybe.monad

infix 2 ⟨_∣_⟩
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

infix 2 ⟨_⟩
mutual

  data Syntax (i : Size) {ℓ : Level} : (A : Set ℓ) → Set (suc ℓ) where
    pure  : (eqDec : RBi.DecSetoid ℓ ℓ) (a : DecSetoid.Carrier eqDec) → Syntax i (DecSetoid.Carrier eqDec)
    token : Syntax i (Lift Char)
    -- _⟨$⟩_ behaves a bit like a constructor.
    -- Indeed the RawPartialIso shaves constructors off / adds them
    _⟨$⟩_ : {A B : Set ℓ} (rpi : RawPartialIso A B) (f : ∞Syntax i A) → Syntax i B
    _⟨✶⟩_ : {A B : Set ℓ} (fa : Syntax i A) (fb : Syntax i B) → Syntax i (A × B)
    _⟨|⟩_ : {A : Set ℓ} (la ra : Syntax i A) → Syntax i A
    ⟨⊘⟩   : {A : Set ℓ} → Syntax i A

  record ∞Syntax (i : Size) {ℓ : Level} (A : Set ℓ) : Set (suc ℓ) where
    coinductive
    field
      force : {j : Size< i} → Syntax i A
open ∞Syntax

⟨_⟩ : {i : Size} {ℓ : Level} {A : Set ℓ} → Syntax i A → ∞Syntax i A
force ⟨ s ⟩ = s

ParserT : {ℓ ℓ′ : Level} (M : Set ℓ → Set ℓ′) (A : Set ℓ) → Set ℓ′
ParserT M A = List Char → M (Maybe (A × List Char))

failParse : {i : Size} {ℓ : Level} {A : Set ℓ} → Delay i (Maybe (A × List Char))
failParse = now nothing

parserBind :
  {i : Size} {ℓ : Level} {A B : Set ℓ} (dm : Delay i (Maybe (A × List Char)))
  (f : A → List Char → Delay i (Maybe (B × List Char))) →
  Delay i (Maybe (B × List Char))
parserBind d f = Delay.bind d $ maybe′ (uncurry f) failParse

mutual

  parser : {i : Size} {ℓ : Level} {A : Set ℓ} (s : Syntax i A) → ParserT (Delay i) A
  parser (pure eq x) xs       = now $ just (x , xs)
  parser token       []       = failParse
  parser token       (x ∷ xs) = now $ just $ lift x , xs
  parser (rpi ⟨$⟩ s) xs       = later (Delay.∞map f′ (∞parser s xs))
    where f′ = flip (M._>>=_) $ uncurry $ λ a ys → Maybe.map (λ b → b , ys) $ push rpi a
  parser (s₁ ⟨✶⟩ s₂) xs       = parserBind (parser s₁ xs) $ λ a ys →
                                parserBind (parser s₂ ys) $ λ b zs →
                                now $ just $ (a , b) , zs
  parser (s₁ ⟨|⟩ s₂) xs       = Delay.bind (parser s₁ xs) $ maybe′ (now ∘ just) (parser s₂ xs)
  parser ⟨⊘⟩         xs       = failParse

  ∞parser : {i : Size} {ℓ : Level} {A : Set ℓ} (s : ∞Syntax i A) → ParserT (∞Delay i) A
  ∞Delay.force (∞parser s xs) {j} = parser (∞Syntax.force s {j}) xs

PrinterT : {ℓ : Level} (M : Set ℓ → Set ℓ) (A : Set ℓ) → Set ℓ
PrinterT M A = A → M (Maybe (Lift $ List Char))

printerReturn : {ℓ : Level} {i : Size} → PrinterT {ℓ} (Delay i) (Lift $ List Char)
printerReturn a = now (just a)

printerFail : {ℓ : Level} {i : Size} → Delay i (Maybe (Set ℓ ∋ Lift (List Char)))
printerFail = now nothing

printerBind :
  {i : Size} {ℓ : Level} (dm : Delay i (Maybe (Set ℓ ∋ Lift (List Char))))
  (f : List Char → Delay i (Maybe (Lift $ List Char))) →
  Delay i (Maybe (Set ℓ ∋ Lift (List Char)))
printerBind d f = Delay.bind d $ maybe′ (f ∘ lower) printerFail

mutual
  printer : {i : Size} {ℓ : Level} {A : Set ℓ} (s : Syntax i A) → PrinterT (Delay i) A
  printer (pure eq x) y = dec (DecSetoid._≟_ eq x y) (const (printerReturn (lift []))) (const printerFail)
  printer token       x = printerReturn (lift $ lower x ∷ [])
  printer (rpi ⟨$⟩ s) x = maybe′ (later ∘ ∞printer s) printerFail (pull rpi x)
  printer (s₁ ⟨✶⟩ s₂) x = printerBind (printer s₁ (proj₁ x)) λ xs →
                          printerBind (printer s₂ (proj₂ x)) λ ys →
                          printerReturn (lift $ xs ++ ys)
  printer (s₁ ⟨|⟩ s₂) x = Delay.bind (printer s₁ x) $ maybe′ (now ∘ just) (printer s₂ x)
  printer ⟨⊘⟩         x = printerFail

  ∞printer : {i : Size} {ℓ : Level} {A : Set ℓ} (s : ∞Syntax i A) → PrinterT (∞Delay i) A
  ∞Delay.force (∞printer s x) {j} = printer (∞Syntax.force s {j}) x

toMaybe : {ℓ : Level} {A : Set ℓ} (xs : List A) → Maybe (A × List A)
toMaybe []       = nothing
toMaybe (x ∷ xs) = just (x , xs)

nil : {ℓ : Level} {A : Set ℓ} → RawPartialIso (Lift ⊤) (List A)
nil = ⟨ const (just []) ∣ foldr (λ _ _ → nothing) (just (lift tt)) ⟩

cons : {ℓ : Level} {A : Set ℓ} → RawPartialIso (A × List A) (List A)
cons = ⟨ just ∘′ uncurry _∷_ ∣ toMaybe ⟩


liftDecSetoid : {c c′ ℓ ℓ′ : Level} → DecSetoid c ℓ → DecSetoid (c ⊔ c′) (ℓ ⊔ ℓ′)
liftDecSetoid {c} {c′} {ℓ} {ℓ′} ds =
  let module DS = DecSetoid ds; open DS
      isEquiv = record { refl  = lift DS.refl
                       ; sym   = lift ∘ DS.sym ∘ lower
                       ; trans = λ x y → lift (DS.trans (lower x) (lower y)) }
      isDec   = λ x y → dec (lower x DS.≟ lower y)
                            (yes ∘ lift)
                            (λ ¬p → no (¬p ∘ lower))
  in
  record { Carrier          = Lift {c} {c′} Carrier
         ; _≈_              = λ x y → Lift {ℓ} {ℓ′} (lower x ≈ lower y)
         ; isDecEquivalence = record { isEquivalence = isEquiv
                                     ; _≟_           = isDec } }

mutual

  many : {i : Size} {ℓ : Level} {A : Set ℓ} → Syntax i A → Syntax i (List A)
  many a =
          cons ⟨$⟩ manyCons a
      ⟨|⟩ nil  ⟨$⟩ justNil

  justNil : {i : Size} {ℓ : Level} → ∞Syntax i (Set ℓ ∋ Lift ⊤)
  force justNil = pure (liftDecSetoid Unit.decSetoid) (lift tt)

  manyCons : {i : Size} {ℓ : Level} {A : Set ℓ} → Syntax i A → ∞Syntax i (A × List A)
  ∞Syntax.force (manyCons a) = a ⟨✶⟩ many a

open import Data.Nat
open import Data.Sum
open import Data.String
open import Data.Nat.Show as Nat
open import Data.Nat.Read

chars : {i : Size} → Syntax i (List Char)
chars = many $ ⟨ just ∘ lower ∣ just ∘ lift ⟩ ⟨$⟩ ⟨ token ⟩

nat : {i : Size} → Syntax i ℕ
nat = ⟨ ([ const nothing , just ]′ ∘ parseℕ ∘ fromList)
      ∣ just ∘′ toList ∘′ Nat.show
      ⟩ ⟨$⟩ ⟨ chars ⟩

test :
  let result = proj₁ $ from-just $ from-just
             $ runDelay 10 $ parser nat $ toList $ "914"
  in result ≡ 914
test = PEq.refl
