module linear.Scope where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Function

data Mergey : (k l : ℕ) → Set where
  finish : {k : ℕ} → Mergey k k
  copy   : {k l : ℕ} → Mergey k l → Mergey (suc k) (suc l)
  insert : {k l : ℕ} → Mergey k l → Mergey k (suc l)

Weakening : (T : ℕ → Set) → Set
Weakening T = {k l : ℕ} (m : Mergey k l) → T k → T l

Extending : (T : ℕ → ℕ → Set) → Set
Extending T = {k l : ℕ} (o : ℕ) → T k l → T (o + k) (o + l)

copys : Extending Mergey
copys zero    m = m
copys (suc o) m = copy (copys o m)

weakFin : Weakening Fin
weakFin finish     k       = k
weakFin (copy m)   zero    = zero
weakFin (copy m)   (suc k) = suc (weakFin m k)
weakFin (insert m) k       = suc (weakFin m k)

data Env (T : ℕ → Set) (l : ℕ) : (k : ℕ) → Set where
  []  : Env T l 0
  _∷_ : {k : ℕ} (t : T l) (ρ : Env T l k) → Env T l (suc k)

weakEnv : {T : ℕ → Set} (weakT : Weakening T) {k : ℕ} → Weakening (flip (Env T) k)
weakEnv weakT inc []      = []
weakEnv weakT inc (t ∷ ρ) = weakT inc t ∷ weakEnv weakT inc ρ

Substituting : (E T : ℕ → Set) → Set
Substituting E T = {k l : ℕ} (ρ : Env E l k) → T k → T l

substFin : {k l : ℕ} {T : ℕ → Set} (ρ : Env T l k) → Fin k → T l
substFin (t ∷ ρ) zero    = t
substFin (t ∷ ρ) (suc v) = substFin ρ v

record Freshey (T : ℕ → Set) : Set where
  field
    fresh : {k : ℕ} → T (suc k)
    weak  : Weakening T

module WithFreshVars {T : ℕ → Set} (F : Freshey T) where

  open Freshey F

  withFreshVars : Extending (Env T)
  withFreshVars zero    ρ = ρ
  withFreshVars (suc o) ρ = fresh ∷ weakEnv weak (insert finish) (withFreshVars o ρ)


  withFreshVar : {k l : ℕ} → Env T l k → Env T (suc l) (suc k)
  withFreshVar = withFreshVars 1
