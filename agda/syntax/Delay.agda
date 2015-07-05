{-# OPTIONS --copatterns #-}
module Delay where

open import Level
open import Size
open import Function

mutual

  data Delay (i : Size) {ℓ : Level} (A : Set ℓ) : Set ℓ where
    now   : A → Delay i A
    later : (d : ∞Delay i A) → Delay i A

  record ∞Delay (i : Size) {ℓ : Level} (A : Set ℓ) : Set ℓ where
    coinductive
    field
      force : {j : Size< i} → Delay j A
open ∞Delay

mutual

  map : {i : Size} {ℓᵃ ℓᵇ : Level} {A : Set ℓᵃ} {B : Set ℓᵇ}
        (f : A → B) (d : Delay i A) → Delay i B
  map f (now a)   = now $ f a
  map f (later d) = later $ ∞map f d

  ∞map : {i : Size} {ℓᵃ ℓᵇ : Level} {A : Set ℓᵃ} {B : Set ℓᵇ}
         (f : A → B) (d : ∞Delay i A) → ∞Delay i B
  force (∞map f d) = map f (force d)

mutual

  bind : {i : Size} {ℓᵃ ℓᵇ : Level} {A : Set ℓᵃ} {B : Set ℓᵇ}
         (d : Delay i A) (f : A → Delay i B) → Delay i B
  bind (now a)   f = f a
  bind (later d) f = later (∞bind d f)

  ∞bind : {i : Size} {ℓᵃ ℓᵇ : Level} {A : Set ℓᵃ} {B : Set ℓᵇ}
          (d : ∞Delay i A) (f : A → Delay i B) → ∞Delay i B
  force (∞bind d f) = bind (force d) f

open import Data.Nat
open import Data.Maybe

runDelay : {ℓ : Level} {A : Set ℓ} (n : ℕ) (d : Delay ∞ A) → Maybe A
runDelay n       (now a)   = just a
runDelay 0       (later d) = nothing
runDelay (suc n) (later d) = runDelay n (force d)