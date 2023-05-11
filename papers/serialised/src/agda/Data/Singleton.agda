{-# OPTIONS --erasure #-}

module Data.Singleton where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b

data Singleton {A : Set a} : (@0 x : A) → Set a where
  mkSingleton : (x : A) → Singleton x

getSingleton : {@0 t : A} → Singleton t → A
getSingleton (mkSingleton t) = t

pure : (t : A) → Singleton t
pure = mkSingleton

_<$>_ : (f : A → B) → {@0 t : A} → Singleton t → Singleton (f t)
f <$> mkSingleton t = mkSingleton (f t)

_<*>_ : ∀ {@0 f : A → B} {@0 t} → Singleton f → Singleton t → Singleton (f t)
mkSingleton f <*> mkSingleton t = mkSingleton (f t)

unsafeMkSingleton : ∀ {@0 x : A} → A → Singleton x
unsafeMkSingleton {x = x} y = coerce x≡y (mkSingleton y) where

  coerce : ∀ {@0 x y : A} → (@0 eq : x ≡ y) → Singleton y → Singleton x
  coerce refl s = s

  postulate @0 x≡y : x ≡ y
