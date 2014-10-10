module lib.Maybe where

open import Level renaming (zero to ze ; suc to su)
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Product hiding (map)
open import Function

returnType bindType mapType appType : ∀ {ℓ} (M : Set ℓ → Set ℓ) → Set (su ℓ)
returnType {ℓ} M = ∀ {A : Set ℓ} (a : A) → M A
bindType   {ℓ} M = ∀ {A B : Set ℓ} (t : M A) (ρ : A → M B) → M B
mapType    {ℓ} M = ∀ {A B : Set ℓ} (f : A → B) (ma : M A) → M B
appType    {ℓ} M = ∀ {A : Set ℓ} (ma₁ ma₂ : M A) → M A

eqType : ∀ {ℓ} → Set ℓ → Set ℓ
eqType A = A → A → Bool

private

  module Dummy where

    data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
      none :           Maybe A
      some : (a : A) → Maybe A

    syntax Maybe A = A ??

open Dummy public hiding (module Maybe)

maybe : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} (s : A → B) (n : B) (ma : Maybe A) → B
maybe s n none     = n
maybe s n (some a) = s a


module Maybe where

  isSome :  ∀ {ℓ} {A : Set ℓ} (ma : Maybe A) → Bool
  isSome = maybe (const true) false

  fromSome : ∀ {ℓ} {A : Set ℓ} (ma : Maybe A) {prf : maybe (const ⊤) ⊥ ma} → A
  fromSome none     = λ {}
  fromSome (some a) = a

  isNone :  ∀ {ℓ} {A : Set ℓ} (ma : Maybe A) → Bool
  isNone = not ∘ isSome

  induction : ∀ {ℓ} {A : Set ℓ} (P : Maybe A → Set)
              (Pn : P none) (Pa : (a : A) → P $ some a) (ma : Maybe A) → P ma
  induction P Pn Pa none     = Pn
  induction P Pn Pa (some a) = Pa a

  map : ∀ {ℓ} → mapType {ℓ} Maybe
  map f = maybe (some ∘ f) none

  bind : ∀ {ℓ} → bindType {ℓ} Maybe
  bind ma f = maybe f none ma

  return : ∀ {ℓ} → returnType {ℓ} Maybe
  return = some

  app : ∀ {ℓ} → appType {ℓ} Maybe
  app none     ma₂ = ma₂
  app (some a) ma₂ = some a

  infix -10 do_
  infixr -5 doBind doMap appMap
  do_ : ∀ {ℓ} {A : Set ℓ} (ma : Maybe A) → Maybe A
  do_ = id

  doBind : ∀ {ℓ} → bindType {ℓ} Maybe
  doBind = bind

  appMap doMap :  ∀ {ℓ} → mapType {ℓ} Maybe
  appMap  = map
  doMap   = map

  syntax appMap f ma         = f <$> ma
  syntax bind ma f           = ma >>= f
  syntax doBind ma (λ x → f) = x ← ma , f
  syntax doMap (λ x → f) ma  = x ←′ ma , f

module Predicates where

  data isSome {ℓ} {A : Set ℓ} : (ma : Maybe A) → Set ℓ where
    some : (a : A) → isSome (some a)

  fromSome : ∀ {ℓ} {A : Set ℓ} {ma : Maybe A} (pr : isSome ma) → A
  fromSome (some a) = a

  bind : ∀ {ℓ} {A B : Set ℓ} {ma : Maybe A} (pr : isSome ma) {f : A → Maybe B} →
         isSome (f $ fromSome pr) → isSome (Maybe.bind ma f)
  bind (some a) pr = pr