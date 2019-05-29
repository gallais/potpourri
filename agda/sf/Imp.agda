-- The content of this file is based on Software Foundations
-- In particular the chapter IMP in Volume 1: Logical Foundations
-- https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html

-- We never hesitate to depart from the text and use typical functional
-- programming techniques, and even Agda-centric techniques as long as
-- they make our life easier.

module Imp where

open import Data.Bool as Bool
import Data.Bool.Properties as Bₚ
open import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ
open import Data.List.Base using ()
open import Data.Maybe
open import Data.Product using (_,_)
open import Data.String.Base
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data Type : Set where
  `ℕ `Bool : Type

private
  variable
    σ τ ν : Type
    σ₁ τ₁ ν₁ : Type
    σ₂ τ₂ ν₂ : Type

⟦_⟧ : Type → Set
⟦ `ℕ    ⟧ = ℕ
⟦ `Bool ⟧ = Bool

infixr 3 _`∧_
infix 4 `¬_
infixr 5 _`≡_ _`≤_
infixr 6 _`+_ _`∸_
infixr 7 _`*_
infix 8 `_

data Op₁ : Type → Type → Set where
  Neg : Op₁ `Bool `Bool

data Op₂ : Type → Type → Type → Set where
  Plus Minus Mult : Op₂ `ℕ `ℕ `ℕ
  Eq Le           : Op₂ `ℕ `ℕ `Bool
  And             : Op₂ `Bool `Bool `Bool

data Imp : Type → Set where
  `_   : ⟦ σ ⟧ → Imp σ
  `Op₁ : Op₁ σ τ → Imp σ → Imp τ
  `Op₂ : Op₂ σ τ ν → Imp σ → Imp τ → Imp ν

pattern _`∧_ e f = `Op₂ And e f
pattern _`≡_ e f = `Op₂ Eq e f
pattern _`≤_ e f = `Op₂ Le e f
pattern _`+_ e f = `Op₂ Plus e f
pattern _`∸_ e f = `Op₂ Minus e f
pattern _`*_ e f = `Op₂ Mult e f
pattern `¬_ e    = `Op₁ Neg e

_ : ` 1 `+ ` 2 `* ` 3 ≡ ` 1 `+ (` 2 `* ` 3)
_ = refl

eval₁ : Op₁ σ τ → ⟦ σ ⟧ → ⟦ τ ⟧
eval₁ Neg = not

eval₂ : Op₂ σ τ ν → ⟦ σ ⟧ → ⟦ τ ⟧ → ⟦ ν ⟧
eval₂ Plus  = _+_
eval₂ Minus = _∸_
eval₂ Mult  = _*_
eval₂ Eq    = λ m n → ⌊ m ℕ.≟ n ⌋
eval₂ Le    = λ m n → ⌊ m ℕ.≤? n ⌋
eval₂ And   = _∧_

eval : Imp σ → ⟦ σ ⟧
eval (` lit)      = lit
eval (`Op₁ o e)   = eval₁ o (eval e)
eval (`Op₂ o e f) = eval₂ o (eval e) (eval f)

_ : eval (` 2 `+ ` 2) ≡ 4
_ = refl

-- Introducing the pattern-matching strategy used by optimize-0+.
-- It allows us to easily prove properties of optimize-0+ by performing
-- what is essentially functional induction

data Opt-0+ : Imp σ → Set where
  0+_ : ∀ e' → Opt-0+ (` 0 `+ e')
  any : {e : Imp σ} → Opt-0+ e

opt-0+ : (e : Imp σ) → Opt-0+ e
opt-0+ (` 0 `+ e) = 0+ e
opt-0+ e = any

optimize-0+   : Imp σ → Imp σ
structural-0+ : Imp σ → Imp σ

optimize-0+ e with opt-0+ e
... | 0+ e' = optimize-0+ e'
... | any   = structural-0+ e

structural-0+ (` lit)      = ` lit
structural-0+ (`Op₁ o e)   = `Op₁ o (optimize-0+ e)
structural-0+ (`Op₂ o e f) = `Op₂ o (optimize-0+ e) (optimize-0+ f)

_ : optimize-0+ (` 2 `+ ` 0 `+ ` 0 `+ ` 1)
  ≡ ` 2 `+ ` 1
_ = refl

optimize-0+-sound : (a : Imp σ) → eval (optimize-0+ a) ≡ eval a
structural-0+-sound : (a : Imp σ) → eval (structural-0+ a) ≡ eval a

optimize-0+-sound e with opt-0+ e
... | 0+ e' = optimize-0+-sound e'
... | any   = structural-0+-sound e

structural-0+-sound (` lit)      = refl
structural-0+-sound (`Op₁ o e)   = cong (eval₁ o) (optimize-0+-sound e)
structural-0+-sound (`Op₂ o e f) =
  cong₂ (eval₂ o) (optimize-0+-sound e) (optimize-0+-sound f)

-- Similarly introducing the pattern-matching strategy used by optimize.

data Opt : Imp σ → Set where
  0+_ : ∀ e' → Opt (` 0 `+ e')
  _+0 : ∀ e' → Opt (e' `+ ` 0)
  0∸_ : ∀ e' → Opt (` 0 `∸ e')
  _∸0 : ∀ e' → Opt (e' `∸ ` 0)
  1*_ : ∀ e' → Opt (` 1 `* e')
  _*1 : ∀ e' → Opt (e' `* ` 1)
  0*_ : ∀ e' → Opt (` 0 `* e')
  _*0 : ∀ e' → Opt (e' `* ` 0)
  ¬¬_ : ∀ b' → Opt (`¬ `¬ b')
  op₁ : ∀ (o : Op₁ σ τ) m → Opt (`Op₁ o (` m))
  op₂ : ∀ (o : Op₂ σ τ ν) m n → Opt (`Op₂ o (` m) (` n))
  any : {e : Imp σ} → Opt e

opt : (e : Imp σ) → Opt e
opt (` 0 `+ e')          = 0+ e'
opt (e' `+ ` 0)          = e' +0
opt (` 0 `∸ e')          = 0∸ e'
opt (e' `∸ ` 0)          = e' ∸0
opt (` 1 `* e')          = 1* e'
opt (e' `* ` 1)          = e' *1
opt (` 0 `* e')          = 0* e'
opt (e' `* ` 0)          = e' *0
opt (`¬ `¬ b')           = ¬¬ b'
opt (`Op₁ o (` m))       = op₁ o m
opt (`Op₂ o (` m) (` n)) = op₂ o m n
opt _ = any


optimize   : Imp σ → Imp σ
structural : Imp σ → Imp σ

-- Note that optimize simplifies the whole expression first and then
-- tries to see whether some additional work can be performed on the
-- top node (the subtrees are already simplified as much as possible)
optimize e with structural e | opt (structural e)
... | _  | 0+ e'     = e'
... | _  | e' +0     = e'
... | _  | 0∸ e'     = ` 0
... | _  | e' ∸0     = e'
... | _  | 1* e'     = e'
... | _  | e' *1     = e'
... | _  | 0* e'     = ` 0
... | _  | e' *0     = ` 0
... | _  | ¬¬ b'     = b'
... | _  | op₁ o m   = ` eval₁ o m
... | _  | op₂ o m n = ` eval₂ o m n
... | e' | any       = e'

structural (` lit)      = ` lit
structural (`Op₁ o e)   = `Op₁ o (optimize e)
structural (`Op₂ o e f) = `Op₂ o (optimize e) (optimize f)

optimize-sound   : (e : Imp σ) → eval (optimize e) ≡ eval e
structural-sound : (e : Imp σ) → eval (structural e) ≡ eval e

-- A lot of the equational proofs could be replaced with a simple
-- rewrite [blah] = prf
-- but it would make the whole proof fairly unreadable

optimize-sound e
  with structural e | structural-sound e | opt (structural e)
... | _ | prf | 0+ e'     = prf
... | _ | prf | e' +0     = begin
  eval e'          ≡˘⟨ ℕₚ.+-identityʳ (eval e') ⟩
  eval (e' `+ ` 0) ≡⟨ prf ⟩
  eval e           ∎
... | _ | prf | 0∸ e'     = begin
  0           ≡˘⟨ ℕₚ.0∸n≡0 (eval e') ⟩
  0 ∸ eval e' ≡⟨ prf ⟩
  eval e      ∎
... | _ | prf | e' ∸0     = prf
... | _ | prf | 1* e'     = begin
  eval e'     ≡˘⟨ ℕₚ.+-identityʳ (eval e') ⟩
  eval e' + 0 ≡⟨ prf ⟩
  eval e      ∎
... | _ | prf | e' *1     = begin
  eval e'     ≡˘⟨ ℕₚ.*-identityʳ (eval e') ⟩
  eval e' * 1 ≡⟨ prf ⟩
  eval e      ∎
... | _ | prf | 0* e'     = prf
... | _ | prf | e' *0     = begin
  0           ≡˘⟨ ℕₚ.*-zeroʳ (eval e') ⟩
  eval e' * 0 ≡⟨ prf ⟩
  eval e      ∎
... | _ | prf | ¬¬ b'     = begin
  eval b'             ≡˘⟨ Bₚ.not-involutive (eval b') ⟩
  not (not (eval b')) ≡⟨ prf ⟩
  eval e              ∎
... | _ | prf | op₁ o m   = prf
... | _ | prf | op₂ o m n = prf
... | _ | prf | any       = prf

structural-sound (` lit)      = refl
structural-sound (`Op₁ o e)   = cong (eval₁ o) (optimize-sound e)
structural-sound (`Op₂ o e f) =
  cong₂ (eval₂ o) (optimize-sound e) (optimize-sound f)
