{-

* Implementing your own system
* Studying the lambda-calculus
* Proving meta results about your theory
* Representing (semi)-decidable formulas to write a solver
* Working in the internal language of a category

-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Data.Product.Base using (_×_; _,_; _,′_)
open import Agda.Builtin.Equality

interleaved mutual
  -------------------
  -- Infrastructure

  data Ty : Set
  variable σ τ : Ty

  data Scope : Set where
    ε : Scope
    _,_ : Scope → Ty → Scope
  variable Γ : Scope

  data DeBruijn : Ty → Scope → Set where
    zero :                DeBruijn σ (Γ , σ)
    succ : DeBruijn σ Γ → DeBruijn σ (Γ , τ)

  Val : Ty → Set

  data Env : Scope → Set where
    ε : Env ε
    _,_ : Env Γ → Val σ → Env (Γ , σ)

  -------------------
  -- Signatures

  data Tm (Γ : Scope) : Ty → Set
  eval : Env Γ → Tm Γ σ → Val σ


  -------------------
  -- Constructors & cases

  data Ty where
    `Nat : Ty

  Val `Nat = Nat

  -- Literals
  data Tm where
    `lit : Nat -> Tm Γ `Nat
  eval ρ (`lit n) = n


  -- Plus
  data Tm where
    `plus : Tm Γ `Nat → Tm Γ `Nat → Tm Γ `Nat

  eval ρ (`plus s t) = eval ρ s + eval ρ t


  -- Var
  data Tm where
    `var : DeBruijn σ Γ → Tm Γ σ

  eval (ρ , v) (`var zero) = v
  eval ε (`var ())
  eval (ρ , _) (`var (succ v)) = eval ρ (`var v)

  -- Pair
  data Ty where
    `Pair : Ty → Ty → Ty

  Val (`Pair σ τ) = Val σ × Val τ

  data Tm where
    `pair : Tm Γ σ → Tm Γ τ → Tm Γ (`Pair σ τ)

  eval ρ (`pair s t) = eval ρ s ,′ eval ρ t


  -- Function
  data Ty where
    `Fun : Ty → Ty → Ty

  Val (`Fun σ τ) = Val σ → Val τ

  data Tm where
    `lam : Tm (Γ , σ) τ → Tm Γ (`Fun σ τ)
    `app : Tm Γ (`Fun σ τ) → Tm Γ σ → Tm Γ τ

  eval ρ (`app f t) = (eval ρ f) (eval ρ t)
  eval ρ (`lam b) = λ v → eval (ρ , v) b
