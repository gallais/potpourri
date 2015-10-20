module cyclicList where

open import Data.Unit
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality

data RawCList (A : Set) : Bool → Set where
  []     : RawCList A true
  var    : RawCList A false
  _∷_    : {b : Bool} (a : A) (as : RawCList A b) → RawCList A b
  fix_∷_ : (a : A) (as : RawCList A false)        → RawCList A true

open import Size

infixr 10 _∷_
mutual

  data CoList (A : Set) (i : Size) : Set where
    []  :                              CoList A i
    _∷_ : (a : A) (as : ∞CoList A i) → CoList A i

  record ∞CoList (A : Set) (i : Size) : Set where
    coinductive
    field force : {j : Size< i} → CoList A j

infix 5 [_]_~_
mutual

  data [_]_~_ {A : Set} (i : Size) : (as bs : CoList A i) → Set where
    []  : [ i ] [] ~ []
    _∷_ : {a b : A} {as bs : ∞CoList A i} → a ≡ b → [ i ] as ∞~ bs → [ i ] a ∷ as ~ b ∷ bs

  record [_]_∞~_ {A : Set} (i : Size) (as bs : ∞CoList A i) : Set where
    coinductive
    field force : {j : Size< i} → [ j ] ∞CoList.force as ~ ∞CoList.force bs

mutual

  ~-refl : {A : Set} {i : Size} (as : CoList A i) → [ i ] as ~ as
  ~-refl []       = []
  ~-refl (a ∷ as) = refl ∷ ∞~-refl as

  ∞~-refl : {A : Set} {i : Size} (as : ∞CoList A i) → [ i ] as ∞~ as
  [_]_∞~_.force (∞~-refl as) = ~-refl (∞CoList.force as)

CList : (A : Set) → Set
CList A = RawCList A true

mutual

  ⟦_⟧_ : {A : Set} {b : Bool} (as : RawCList A b) (tl : if b then ⊤ else A × RawCList A false)
         {i : Size} → CoList A i
  ⟦ []         ⟧ tl       = []
  ⟦ var        ⟧ (a , tl) = a ∷ ∞⟦ tl ⟧ (a , tl)
  ⟦ a ∷ as     ⟧ tl       = a ∷ ∞⟦ as ⟧ tl
  ⟦ fix a ∷ as ⟧ tl       = a ∷ ∞⟦ as ⟧ (a , as)

  ∞⟦_⟧_ : {A : Set} {b : Bool} (as : RawCList A b) (tl : if b then ⊤ else A × RawCList A false)
          {i : Size} → ∞CoList A i
  ∞CoList.force (∞⟦ as ⟧ tl) = ⟦ as ⟧ tl

toCoList : {A : Set} (as : CList A) → CoList A ∞
toCoList as = ⟦ as ⟧ tt

mapRCL : {A B : Set} (f : A → B) {b : Bool} (as : RawCList A b) → RawCList B b
mapRCL f []           = []
mapRCL f var          = var
mapRCL f (a ∷ as)     = f a ∷ mapRCL f as
mapRCL f (fix a ∷ as) = fix f a ∷ mapRCL f as

mapTl : {A B : Set} (f : A → B) {b : Bool} (tl : if b then ⊤ else A × RawCList A false) →
         if b then ⊤ else B × RawCList B false
mapTl f {true}  tl       = tt
mapTl f {false} (a , tl) = f a , mapRCL f tl

mutual

  mapCL : {A B : Set} (f : A → B) {i : Size} (as : CoList A i) → CoList B i
  mapCL f []       = []
  mapCL f (a ∷ as) = f a ∷ ∞mapCL f as
  
  ∞mapCL : {A B : Set} (f : A → B) {i : Size} (as : ∞CoList A i) → ∞CoList B i
  ∞CoList.force (∞mapCL f as) = mapCL f (∞CoList.force as)


⟦map⟧ : {A B : Set} (f : A → B) (as : CList A) →
        [ ∞ ] toCoList (mapRCL f as) ~ mapCL f (toCoList as)
⟦map⟧ {A} f as = go as tt where

  mutual

    go : {b : Bool} (as : RawCList A b) (tl : if b then ⊤ else A × RawCList A false) →
         {i : Size} → [ i ] (⟦ mapRCL f as ⟧ (mapTl f {b} tl)) ~ mapCL f (⟦ as ⟧ tl)
    go []           tl       = []
    go var          (a , as) = refl ∷ ∞go as (a , as)
    go (a ∷ as)     tl       = refl ∷ ∞go as tl
    go (fix a ∷ as) tl       = refl ∷ ∞go as (a , as)
 
    ∞go : {b : Bool} (as : RawCList A b) (tl : if b then ⊤ else A × RawCList A false) →
          {i : Size} → [ i ] (∞⟦ mapRCL f as ⟧ (mapTl f {b} tl)) ∞~ ∞mapCL f (∞⟦ as ⟧ tl)
    [_]_∞~_.force (∞go as tl) = go as tl
