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

data Env (T : ℕ → Set) : (k l : ℕ) → Set where
  []  : {l : ℕ} → Env T 0 l
  v∷_ : {k l : ℕ} → Env T k l → Env T (suc k) (suc l)
  _∷_ : {k l : ℕ} (t : T l) (ρ : Env T k l) → Env T (suc k) l

Substituting : (E T : ℕ → Set) → Set
Substituting E T = {k l : ℕ} (ρ : Env E k l) → T k → T l

record Freshey (T : ℕ → Set) : Set where
  field
    fresh : {k : ℕ} → T (suc k)
    weak  : Weakening T

substFin : {k l : ℕ} {T : ℕ → Set} (F : Freshey T) (ρ : Env T k l) → Fin k → T l
substFin F (v∷ ρ)  zero    = Freshey.fresh F
substFin F (t ∷ ρ) zero    = t
substFin F (v∷ ρ)  (suc v) = Freshey.weak F (insert finish) $ substFin F ρ v
substFin F (t ∷ ρ) (suc v) = substFin F ρ v

withFreshVars : {T : ℕ → Set} → Extending (Env T)
withFreshVars zero    ρ = ρ
withFreshVars (suc o) ρ = v∷ withFreshVars o ρ
