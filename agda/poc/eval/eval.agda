-- The content of this file is an attempt at formalizing an
-- evaluation mechanism similar to the one described in the
-- following blog post:
-- http://siek.blogspot.co.uk/2013/05/type-safety-in-three-easy-lemmas.html

-- One of the particularities is that we work in the partiality
-- monad except that we use an applicative instance not derived
-- from the monad one. In effect, that means that we only spend
-- fuel on the recursion depth rather than on the length of the
-- evaluation (_>>=_, unlike _⊛_,  accumulates all the delays!).
-- This could be useful to implement e.g. Coq's auto in Agda in
-- terms of the delay monad rather than via the fuel-threading
-- technique used in:
-- https://github.com/pepijnkokke/AutoInAgda

module eval where

open import Level
open import Coinduction
open import Category.Functor
open import Category.Applicative
open import Function

-- The delay monad
data Delay {ℓ} (A : Set ℓ) : Set ℓ where
  now!  : (a : A) → Delay A
  later : (da : ∞ (Delay A)) → Delay A

-- bind
_>>=_ : {ℓᵃ ℓᵇ : Level} {A : Set ℓᵃ} {B : Set ℓᵇ} (da : Delay A) (f : A → Delay B) → Delay B
now!  a  >>= f = f a
later da >>= f = later (♯ (♭ da >>= f))

-- functor instance
isRawFunctorDelay : ∀ {ℓ} → RawFunctor (Delay {ℓ})
isRawFunctorDelay = record { _<$>_ = fmap }
  where
    fmap : {ℓ : Level} {A B : Set ℓ} (f : A → B) (da : Delay A) → Delay B
    fmap f (now! a)   = now! (f a)
    fmap f (later xs) = later (♯ fmap f (♭ xs))

-- applicative instance which is *NOT* derived from bind & return
isRawApplicativeDelay : ∀ {ℓ} → RawApplicative (Delay {ℓ})
isRawApplicativeDelay = record { pure = now!
                               ; _⊛_  = sync }
  where
    sync : {ℓ : Level} {A B : Set ℓ} (df : Delay (A → B)) (dx : Delay A) → Delay B
    sync (now! f)  (now! a)  = now!  $ f a
    sync (now! f)  (later a) = later (♯ sync (now! f) (♭ a))
    sync (later f) (now! a)  = later (♯ sync (♭ f) (now! a))
    sync (later f) (later a) = later (♯ sync (♭ f) (♭ a))

module AD = RawApplicative (isRawApplicativeDelay {zero})
open AD

open import Data.Nat as Nat
open import Data.Fin as Fin
open import Data.Vec as Vec hiding (_⊛_ ; _>>=_)
open import Data.Bool
open import Data.Product
open import Relation.Nullary.Decidable

-- Little (untyped) language
data Op : Set where
  `+ `* `= : Op

data Term (n : ℕ) : Set where
  `Nat  : ℕ    → Term n
  `Bool : Bool → Term n
  `Op   : (l : Term n) (op : Op) (r : Term n) → Term n
  `var  : (k : Fin n) → Term n
  -- the intuition behind the recursive definition:
  -- rec f x $ t ~~~> f [rec f x / f, t / x]
  `rec  : (b : Term (2 Nat.+ n)) → Term n
  `app  : (f t : Term n) → Term n

-- Because the language is untyped, evaluation may crash:
data Result (A : Set) : Set where
  value : (a : A) → Result A
  stuck : Result A

fmap2 : {A B C : Set} (f : A → B → C) (a : Result A) (b : Result B) → Result C
fmap2 f (value a) (value b) = value $ f a b
fmap2 f _         stuck     = stuck
fmap2 f stuck     _         = stuck

-- Values are either constants or closures
data Value : Set where
  `Nat     : ℕ → Value
  `Bool    : Bool → Value
  `Closure : {n : ℕ} (b : Term (2 Nat.+ n)) (ρ : Vec Value n) → Value

-- The outcome of the evaluation is a delayed result
Outcome : (A : Set) → Set
Outcome A = Delay (Result A)

return : Value → Outcome Value
return = now! ∘ value

_`_`_ : {A B C : Set} (a : A) (f : A → B → C) (b : B) → C
a ` f ` b = f a b

-- We may expect nats
toNat : Result Value → Result ℕ
toNat (value (`Nat n)) = value n
toNat _                = stuck

lift2Delay : {A B C : Set} (f : A → B → C) → Delay A → Delay B → Delay C
lift2Delay f da db = pure f ⊛ da ⊛ db

lift2Value : {A : Set} (c : A → Value) (f : ℕ → ℕ → A) → Result Value → Result Value → Result Value
lift2Value c f v₁ v₂ = fmap2 (λ m → c ∘ f m) (toNat v₁) (toNat v₂)

-- Ops can be given a meaning 
δ : Op → Delay (Result Value) → Delay (Result Value) → Delay (Result Value)
δ `+ = lift2Delay $ lift2Value `Nat Nat._+_
δ `* = lift2Delay $ lift2Value `Nat Nat._*_ 
δ `= = lift2Delay $ lift2Value `Bool $ λ m n → ⌊ m Nat.≟ n ⌋

-- evaluation is defined mutually with application
-- which restarts closures
-- TODO try to use NAD's trick:
-- http://www.cse.chalmers.se/~nad/publications/danielsson-productivity.html

mutual

  app : Result Value → Result Value → Outcome Value
  app (value (`Closure b ρ)) (value u) = ⟦ b ⟧ (u ∷ (`Closure b ρ) ∷ ρ)
  app t                      u         = now! stuck

  ⟦_⟧_ : {n : ℕ} (t : Term n) (ρ : Vec Value n) → Outcome Value
  ⟦ `Nat n     ⟧ ρ = return $ `Nat n
  ⟦ `Bool b    ⟧ ρ = return $ `Bool b
  ⟦ `Op t op u ⟧ ρ = ⟦ t ⟧ ρ ` δ op ` ⟦ u ⟧ ρ
  ⟦ `var k     ⟧ ρ = return $ Vec.lookup k ρ
  ⟦ `rec t     ⟧ ρ = return $ `Closure t ρ
  ⟦ `app t u   ⟧ ρ = (pure _,_ ⊛ ⟦ t ⟧ ρ ⊛ ⟦ u ⟧ ρ) >>= uncurry (λ vt vu → later (♯ app vt vu))