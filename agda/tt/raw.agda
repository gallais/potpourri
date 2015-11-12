{-# OPTIONS --copatterns #-}

module tt.raw where

open import Data.Nat as ℕ
open import Data.Fin hiding (_<_)
open import Function

mutual

  record Type (n : ℕ) : Set where
    inductive
    constructor El
    field
      unEl : Check n

  data Check (n : ℕ) : Set where
    -- types
    `sig : (A : Type n) (B : Type (suc n)) → Check n
    `pi  : (A : Type n) (B : Type (suc n)) → Check n
    `nat :                                   Check n
    `set : ℕ                               → Check n
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

open Type public

var₀ : {n : ℕ} → Check (suc n)
var₀ = `emb (`var zero)

set : {n : ℕ} (ℓ : ℕ) → Type n
unEl (set ℓ) = `set ℓ

nat : {n : ℕ} → Type n
nat = El `nat

sig : {n : ℕ} → Type n → Type (suc n) → Type n
unEl (sig A B) = `sig A B

pi : {n : ℕ} → Type n → Type (suc n) → Type n
unEl (pi A B) = `pi A B
