module lib.Fin where

open import Level using (Level)
open import Data.Nat
open import Data.Fin

Fin-case : {ℓ : Level} {n : ℕ} {P : Fin (suc n) → Set ℓ}
           (p0 : P zero) (pS : (k : Fin n) → P (suc k)) →
           (k : Fin (suc n)) → P k
Fin-case p0 pS zero    = p0
Fin-case p0 pS (suc k) = pS k

Fin0-elim : {ℓ : Level} {A : Set ℓ} (hf : Fin 0) → A
Fin0-elim ()