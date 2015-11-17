{-# OPTIONS --copatterns #-}

module tt.raw where

open import Data.Nat as ℕ
open import Data.Fin hiding (_<_)
open import Function
open import Relation.Binary.PropositionalEquality

-----------------------------------------------------------
-- SYNTAX
-----------------------------------------------------------


mutual

  data Type (n : ℕ) : Set where
    -- types
    `sig : (A : Type n) (B : Type (suc n)) → Type n
    `pi  : (A : Type n) (B : Type (suc n)) → Type n
    `nat :                                   Type n
    `set : ℕ                               → Type n
    `elt : (e : Infer n)                   → Type n

  data Check (n : ℕ) : Set where
    `typ : (A : Type n)                    → Check n
    -- lambda abstraction
    `lam : (b : Check (suc n))             → Check n
    -- constructors
    `per : (a b : Check n)                 → Check n
    `zro :                                   Check n
    `suc : (m : Check n)                   → Check n
    -- embedding
    `emb : (e : Infer n)                   → Check n

  data Infer (n : ℕ) : Set where
    -- head symbol
    `var : (k : Fin n)                                → Infer n
    `ann : (t : Check n) (A : Type n)                 → Infer n
    -- eliminators
    `app : (t : Infer n) (u : Check n)                → Infer n
    `fst : (t : Infer n)                              → Infer n
    `snd : (t : Infer n)                              → Infer n
    `ind : (p z s : Check n) (m : Infer n) → Infer n

-----------------------------------------------------------
-- SMART CONSTRUCTORS
-----------------------------------------------------------

var₀ : {n : ℕ} → Check (suc n)
var₀ = `emb (`var zero)

appC : {n : ℕ} → Check n → Type n → Check n → Check n
appC t T u = `emb (`app (`ann t T) u)

appT : {n : ℕ} → Check n → Type n → Check n → Type n
appT t T u = `elt (`app (`ann t T) u)

-----------------------------------------------------------
-- INVERSION LEMMAS
-----------------------------------------------------------

`var-inj : {m : ℕ} {k l : Fin m} → `var k ≡ `var l → k ≡ l
`var-inj refl = refl

