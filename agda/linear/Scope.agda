module linear.Scope where

open import Data.Nat
open import Data.Fin hiding (_+_)

Scope = ℕ

data Mergey : (k l : ℕ) → Set where
  finish : {k : ℕ} → Mergey k k
  copy   : {k l : ℕ} → Mergey k l → Mergey (suc k) (suc l)
  insert : {k l : ℕ} → Mergey k l → Mergey k (suc l)

copys : (o : ℕ) {k l : ℕ} → Mergey k l → Mergey (o + k) (o + l)
copys zero    m = m
copys (suc o) m = copy (copys o m)

weakFin : {k l : ℕ} (m : Mergey k l) → Fin k → Fin l
weakFin finish     k       = k
weakFin (copy m)   zero    = zero
weakFin (copy m)   (suc k) = suc (weakFin m k)
weakFin (insert m) k       = suc (weakFin m k)
