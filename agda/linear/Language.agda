module linear.Language where

open import Data.Nat as ℕ
open import Data.Fin
open import Data.Vec hiding ([_])

open import linear.Type
open import linear.Scope as Sc hiding (Env)
open import linear.Context hiding (Mergey ; copys)

mutual

  data Check (n : ℕ) : Set where
    `lam_        : (b : Check (suc n)) → Check n
    `let_∷=_`in_ : {o : ℕ} (p : Pattern o) (t : Infer n) (u : Check (o ℕ.+ n)) → Check n
    `prd         : (a b : Check n) → Check n
    `inl_        : (t : Check n) → Check n
    `inr_        : (t : Check n) → Check n
    `neu_        : (t : Infer n) → Check n

  data Infer (n : ℕ) : Set where
    `var                : (k : Fin n) → Infer n
    `app                : (t : Infer n) (u : Check n) → Infer n
    `case_return_of_%%_ : (i : Infer n) (σ : Type) (l r : Check (suc n)) → Infer n
    `cut                : (t : Check n) (σ : Type) → Infer n

  data Pattern : (m : ℕ) → Set where
    `v   : Pattern 1
    _,,_ : {m n : ℕ} (p : Pattern m) (q : Pattern n) → Pattern (m ℕ.+ n)

-- hack
patternSize : {m : ℕ} → Pattern m → ℕ
patternSize {m} _ = m

mutual

  weakCheck : Weakening Check
  weakCheck inc (`lam b)            = `lam weakCheck (copy inc) b
  weakCheck inc (`let p ∷= t `in u) = `let p ∷= weakInfer inc t `in weakCheck (copys (patternSize p) inc) u
  weakCheck inc (`prd a b)          = `prd (weakCheck inc a) (weakCheck inc b)
  weakCheck inc (`inl t)            = `inl weakCheck inc t
  weakCheck inc (`inr t)            = `inr weakCheck inc t
  weakCheck inc (`neu t)            = `neu weakInfer inc t

  weakInfer : Weakening Infer
  weakInfer inc (`var k)                     = `var (weakFin inc k)
  weakInfer inc (`app i u)                   = `app (weakInfer inc i) (weakCheck inc u)
  weakInfer inc (`case i return σ of l %% r) = `case weakInfer inc i return σ of weakCheck (copy inc) l
                                                                              %% weakCheck (copy inc) r
  weakInfer inc (`cut t σ)                   = `cut (weakCheck inc t) σ


Env = Sc.Env Infer

fresheyInfer : Freshey Infer
fresheyInfer = record { fresh = `var zero ; weak = weakInfer }

mutual

  substCheck : Substituting Infer Check
  substCheck ρ (`lam b)            = `lam substCheck (v∷ ρ) b
  substCheck ρ (`let p ∷= t `in u) = `let p ∷= substInfer ρ t `in substCheck (withFreshVars (patternSize p) ρ) u
  substCheck ρ (`prd a b)          = `prd (substCheck ρ a) (substCheck ρ b)
  substCheck ρ (`inl t)            = `inl substCheck ρ t
  substCheck ρ (`inr t)            = `inr substCheck ρ t
  substCheck ρ (`neu t)            = `neu substInfer ρ t
  
  substInfer : Substituting Infer Infer
  substInfer ρ (`var k)                     = substFin fresheyInfer ρ k
  substInfer ρ (`app i u)                   = `app (substInfer ρ i) (substCheck ρ u)
  substInfer ρ (`case i return σ of l %% r) = `case substInfer ρ i return σ
                                                 of substCheck (v∷ ρ) l
                                                 %% substCheck (v∷ ρ) r
  substInfer ρ (`cut t σ)                   = `cut (substCheck ρ t) σ
