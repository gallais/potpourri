{-# OPTIONS --copatterns #-}

module poc.delay where

open import Level
open import Category.Functor
open import Category.Applicative
open import Function
open import Size

mutual
  -- The delay monad
  record Delay {ℓ : Level} (i : Size) (A : Set ℓ) : Set ℓ where
    coinductive
    constructor [_]
    field
      force : {j : Size< i} → [Delay j , A ]

  data [Delay_,_] {ℓ : Level} (i : Size) (A : Set ℓ) : Set ℓ where
    now!_  : (a : A)          → [Delay i , A ]
    later_ : (da : Delay i A) → [Delay i , A ]

open Delay public

mutual

  [fmap] : {ℓᵃ ℓᵇ : Level} {i : Size} {A : Set ℓᵃ} {B : Set ℓᵇ}
           (f : A → B) (da : [Delay i , A ]) → [Delay i , B ]
  [fmap] f (now!   a) = now!  f a
  [fmap] f (later da) = later fmap f da

  fmap : {ℓᵃ ℓᵇ : Level} {i : Size} {A : Set ℓᵃ} {B : Set ℓᵇ} (f : A → B) (da : Delay i A) → Delay i B
  force (fmap f da) = [fmap] f (force da)

isRawFunctor : {ℓ : Level} {i : Size} → RawFunctor {ℓ} (Delay i)
isRawFunctor = record { _<$>_ = fmap }

pure : {ℓᵃ : Level} {i : Size} {A : Set ℓᵃ} (a : A) → Delay i A
force (pure a) = now! a

delay : {ℓᵃ : Level} {i : Size} {A : Set ℓᵃ} (da : Delay i A) → Delay (↑ i) A
force (delay da) = later da

mutual

  [app] : {ℓᵃ ℓᵇ : Level} {i : Size} {A : Set ℓᵃ} {B : Set ℓᵇ}
          (df : [Delay i , (A → B) ]) (da : [Delay i , A ]) → [Delay i , B ]
  [app] (now! f)   (now! a)   = now! f a
  [app] (later df) (later da) = later app df da
  [app] (later df) da         = later app df [ da ]
  [app] df         (later da) = later app [ df ] da

  app : {ℓᵃ ℓᵇ : Level} {i : Size} {A : Set ℓᵃ} {B : Set ℓᵇ} (df : Delay i (A → B)) (da : Delay i A) → Delay i B
  force (app df da) = [app] (force df) (force da)

isRawApplicative : {ℓ : Level} {i : Size} → RawApplicative {ℓ} (Delay i)
isRawApplicative = record { pure = pure ; _⊛_ = app }


mutual

  _[>>=]_ : {ℓᵃ ℓᵇ : Level} {i : Size} {A : Set ℓᵃ} {B : Set ℓᵇ}
            (da : [Delay i , A ]) (f : A → [Delay i , B ]) → [Delay i , B ]
  (now! a)   [>>=] f = f a
  (later da) [>>=] f = later (da >>= f)

  _>>=_ : {ℓᵃ ℓᵇ : Level} {i : Size} {A : Set ℓᵃ} {B : Set ℓᵇ} (da : Delay i A) (f : A → [Delay i , B ]) → Delay i B
  force (da >>= f) = force da [>>=] f

open import Data.Nat
open import Data.Maybe


mutual

  run[Delay] : {ℓᵃ : Level} {A : Set ℓᵃ} → ℕ → [Delay ∞ , A ] → Maybe A
  run[Delay] n         (now! a)   = just a
  run[Delay] ℕ.zero    (later da) = nothing
  run[Delay] (ℕ.suc n) (later da) = runDelay n da

  runDelay : {ℓᵃ : Level} {A : Set ℓᵃ} → ℕ → Delay ∞ A → Maybe A
  runDelay n da = run[Delay] n (force da)