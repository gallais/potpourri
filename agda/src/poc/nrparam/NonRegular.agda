module NonRegular where

open import Data.Sum
open import Data.Product
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec as Vec
open import Function

_+_ : ℕ → Set → Set
n + A = Fin n ⊎ A

module NonRegularParameter where

  data Lam (A : Set) : Set where
    `var      : (a : A) → Lam A
    `app      : (t u : Lam A) → Lam A
    `lam      : (t : Lam (1 + A)) → Lam A
    `let_`in_ : {n : ℕ} (t : Vec (Lam A) n) (u : Lam (n + A)) → Lam A

module LargeIndex where

  data Lam : (A : Set) → Set₁ where
    `var      : {A : Set} (a : A) → Lam A
    `app      : {A : Set} (t u : Lam A) → Lam A
    `lam      : {A : Set} (t : Lam (1 + A)) → Lam A
    `let_`in_ : {A : Set} {n : ℕ} (t : Vec (Lam A) n) (u : Lam (n + A)) → Lam A

module SmallEncoding where

  data path : Set where
    `rt : path
    `bd : (n : ℕ) (p : path) → path

  decode : (p : path) (A : Set) → Set
  decode `rt       A = A
  decode (`bd n p) A = n + decode p A

  data Lam (A : Set) : path → Set where
    `var      : {p : path} (a : decode p A) → Lam A p
    `app      : {p : path} (t u : Lam A p) → Lam A p
    `lam      : {p : path} (t : Lam A (`bd 1 p)) → Lam A p
    `let_`in_ : {p : path} {n : ℕ} (t : Vec (Lam A p) n) (u : Lam A (`bd n p)) →
                Lam A p

  LamTop : (A : Set) → Set
  LamTop A = Lam A `rt

module IsEquivalent where

  module SE = SmallEncoding
  open SE
  module NRP = NonRegularParameter
  open NRP

  mutual

    NRPtoSE : {A : Set} {p : path} (t : NRP.Lam $ decode p A) → SE.Lam A p
    NRPtoSE (`var a)        = `var a
    NRPtoSE (`app t u)      = SE.`app (NRPtoSE t) $ NRPtoSE u
    NRPtoSE (`lam t)        = SE.`lam $ NRPtoSE t
    NRPtoSE (`let ts `in u) = `let NRPtoSEs ts `in NRPtoSE u

    NRPtoSEs : {A : Set} {p : path} {n : ℕ} (ts : Vec (NRP.Lam $ decode p A) n) →
               Vec (SE.Lam A p) n
    NRPtoSEs []       = []
    NRPtoSEs (t ∷ ts) = NRPtoSE t ∷ NRPtoSEs ts

  mutual

    SEtoNRP : {A : Set} {p : path} (t : SE.Lam A p) → NRP.Lam $ decode p A
    SEtoNRP (`var a)        = `var a
    SEtoNRP (`app t u)      = NRP.`app (SEtoNRP t) $ SEtoNRP u
    SEtoNRP (`lam t)        = NRP.`lam $ SEtoNRP t
    SEtoNRP (`let ts `in u) = `let SEtoNRPs ts `in SEtoNRP u

    SEtoNRPs : {A : Set} {p : path} {n : ℕ} (t : Vec (SE.Lam A p) n) →
               Vec (NRP.Lam $ decode p A) n
    SEtoNRPs []       = []
    SEtoNRPs (t ∷ ts) = SEtoNRP t ∷ SEtoNRPs ts

  open import Relation.Binary.PropositionalEquality

  mutual

    prf₁ : {A : Set} (p : path) (t : NRP.Lam $ decode p A) →
           t ≡ SEtoNRP (NRPtoSE {A = A} {p = p} t)
    prf₁ p (`var a)        = refl
    prf₁ p (`app t u)      = cong₂ `app (prf₁ p t) (prf₁ p u)
    prf₁ p (`lam t)        = cong `lam $ prf₁ (`bd 1 p) t
    prf₁ p (`let ts `in u) = cong₂ `let_`in_ (prfs₁ p ts) $ prf₁ (`bd _ p) u

    prfs₁ : {A : Set} (p : path) {n : ℕ} (ts : Vec (NRP.Lam $ decode p A) n) →
            ts ≡ SEtoNRPs (NRPtoSEs {A = A} {p = p} ts)
    prfs₁ p []       = refl
    prfs₁ p (t ∷ ts) = cong₂ _∷_ (prf₁ p t) $ prfs₁ p ts

  mutual

    prf₂ : {A : Set} (p : path) (t : SE.Lam A p) →
           t ≡ NRPtoSE (SEtoNRP {A = A} {p = p} t)
    prf₂ p (`var a)        = refl
    prf₂ p (`app t u)      = cong₂ `app (prf₂ p t) (prf₂ p u)
    prf₂ p (`lam t)        = cong `lam $ prf₂ (`bd 1 p) t
    prf₂ p (`let ts `in u) = cong₂ `let_`in_ (prfs₂ p ts) $ prf₂ (`bd _ p) u

    prfs₂ : {A : Set} (p : path) {n : ℕ} (ts : Vec (SE.Lam A p) n) →
            ts ≡ NRPtoSEs (SEtoNRPs {A = A} {p = p} ts)
    prfs₂ p []       = refl
    prfs₂ p (t ∷ ts) = cong₂ _∷_ (prf₂ p t) $ prfs₂ p ts