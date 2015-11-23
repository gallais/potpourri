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


mutual

  data Type_≡^Con_ {n : ℕ} : (A B : Type n) → Set where
    `sig : {A₁ A₂ : Type n} {B₁ B₂ : Type (suc n)} → Type `sig A₁ B₁ ≡^Con `sig A₂ B₂
    `pi  : {A₁ A₂ : Type n} {B₁ B₂ : Type (suc n)} → Type `pi  A₁ B₁ ≡^Con `pi  A₂ B₂
    `nat :                                           Type `nat       ≡^Con `nat
    `set : (ℓ : ℕ)                                 → Type `set ℓ     ≡^Con `set ℓ
    ̀elt : {e f : Infer n} → Infer e ≡^Con f       → Type `elt e     ≡^Con `elt f 

  data Check_≡^Con_ {n : ℕ} : (A B : Check n) → Set where
    `typ : {A B : Type n} → Type A ≡^Con B   → Check `typ A   ≡^Con `typ B
    `lam : {b c : Check (suc n)}             → Check `lam b   ≡^Con `lam c
    `per : {a b c d : Check n}               → Check `per a b ≡^Con `per c d
    `zro :                                     Check `zro     ≡^Con `zro
    `suc : {l m : Check n}                   → Check `suc l   ≡^Con `suc m
    `emb : {e f : Infer n} → Infer e ≡^Con f → Check `emb e   ≡^Con `emb f

  data Infer_≡^Con_ {n : ℕ} : (A B : Infer n) → Set where
    `var : {k : Fin n}                                       → Infer `var k   ≡^Con `var k
    `app : {s t : Infer n} {u v : Check n} → Infer s ≡^Con t → Infer `app s u ≡^Con `app t v
    `fst : {s t : Infer n} → Infer s ≡^Con t                 → Infer `fst s   ≡^Con `fst t
    `snd : {s t : Infer n} → Infer s ≡^Con t                 → Infer `snd s   ≡^Con `snd t
    `ind : {p q z a s t : Check n} {l m : Infer n} → Infer l ≡^Con m → Infer `ind p z s l ≡^Con `ind q a t m

