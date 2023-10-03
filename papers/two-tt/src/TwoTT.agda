{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The content of this module is based on the paper
-- Staged compilation with two-level type theory
-- by András Kovács
-- https://dl.acm.org/doi/abs/10.1145/3547641
--
-- and some classic techniques to represent intrinsically-typed calculi
------------------------------------------------------------------------

module TwoTT where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product as Prod using (_×_; _,_)

open import Function.Base using (_∘_; id; const)
open import Relation.Unary using (IUniversal; _⇒_; _⊢_; _∩_)

------------------------------------------------------------------------
-- We have two phases: source code and staged code

data Phase : Set where
  source staged : Phase

variable ph : Phase

------------------------------------------------------------------------
-- We have two stages: static and dynamic

data Stage : Phase → Set where
  static : Stage source
  dynamic : Stage ph

variable st : Stage ph

module Contexts (T : ∀ {ph} → Stage ph → Set) where

  private
    variable A B : T st

  ------------------------------------------------------------------------
  -- Context are your usual left-nested lists of types.
  -- Note the existential quantification over the stage of the freshly
  -- bound variable in the snoc case

  infixl 4 _,_

  data Context : Set where
    ε    : Context
    _,_  : Context → T st → Context

  variable
    Γ Δ θ : Context

  ------------------------------------------------------------------------
  -- Thinnings

  infix 0 _≤_

  data _≤_ : Context → Context → Set where
    done  : ε ≤ ε
    keep  : Γ ≤ Δ → Γ , A ≤ Δ , A
    drop  : Γ ≤ Δ → Γ ≤ Δ , A

  ≤-trans : Γ ≤ Δ → Δ ≤ θ → Γ ≤ θ
  ≤-trans p (drop q) = drop (≤-trans p q)
  ≤-trans done done = done
  ≤-trans (keep p) (keep q) = keep (≤-trans p q)
  ≤-trans (drop p) (keep q) = drop (≤-trans p q)

  ≤-refl : ∀ {Γ} → Γ ≤ Γ
  ≤-refl {ε} = done
  ≤-refl {Γ , x} = keep ≤-refl

  ------------------------------------------------------------------------
  -- Variables (could be defined as thinning from a singleton list)

  data Var : T st → Context → Set where
    here   : ∀[          (_, A) ⊢ Var A ]
    there  : ∀[ Var A ⇒  (_, B) ⊢ Var A ]

  weak-Var : Γ ≤ Δ → Var A Γ → Var A Δ
  weak-Var (drop σ) v = there (weak-Var σ v)
  weak-Var (keep σ) here = here
  weak-Var (keep σ) (there v) = there (weak-Var σ v)

  ------------------------------------------------------------------------
  -- Semantics toolkit: Kripke function spaces between
  -- context-indexed type families

  record □ (A : Context → Set) (Γ : Context) : Set where
    constructor mkBox
    field runBox : ∀ {Δ} → Γ ≤ Δ → A Δ
  open □ public

  Kripke : (A B : Context → Set) (Γ : Context) → Set
  Kripke A B = □ (A ⇒ B)

  -- Action of thinnings on Kripke functions spaces
  -- By construction they're the Free thinnable
  weak-Kripke : ∀ {A B} → Γ ≤ Δ → Kripke A B Γ → Kripke A B Δ
  weak-Kripke σ f .runBox = f .runBox ∘ ≤-trans σ

  -- lambda-abstraction
  infixr 3 mkBox
  syntax mkBox (λ σ x → b) = λλ[ σ , x ] b

  -- application
  _$$_ : ∀ {A B} → Kripke A B Γ → A Γ → B Γ
  f $$ t = f .runBox ≤-refl t

infixr 10 _`×_
infixr 5 _`⇒_


-- We define everything in a big `interleaved mutual` block which
-- allows us to give data constructors and function clauses in
-- successive block.
-- This way we can present a core language that is progressively
-- extended with more and more features:
-- 1. Base STLC
-- 2. Adding quotes and splices for 2-level programming
-- 3. Adding natural numbers (at both stages)
-- 4. Adding pairs (only in the static stage)
interleaved mutual

  ----------------------------------------------------------------------
  -- Base STLC
  ----------------------------------------------------------------------

  ----------------------------------------------------------------------
  -- Types are indexed by the stage they are defined at
  -- Our base type α is available at both stages.
  -- Function types are homogeneous: both domains and codomains need
  -- to live at the same stage.
  data Type : Stage ph → Set where
    `α   : Type st
    _`⇒_ : (A B : Type st) → Type st

  variable
    A : Type st
    B : Type st
    C : Type st

  -- Purely dynamic types still make sense in the staged phase
  asStaged : Type {source} dynamic → Type {staged} dynamic
  asStaged `α        = `α
  asStaged (A `⇒ B)  = asStaged A `⇒ asStaged B

  open Contexts Type

  ----------------------------------------------------------------------
  -- Terms are indexed both by the stage of the type of the computation
  -- they describe but also by a boolean describing whether it is legal
  -- to uses quotes and splices
  data Term : (ph : Phase) → (st : Stage ph) → Type st → Context → Set where
    `var   : ∀[ Var A ⇒ Term ph st A ]
    `app   : ∀[ Term ph st (A `⇒ B) ⇒ Term ph st A ⇒ Term ph st B ]
    `lam   : ∀[ (_, A) ⊢ Term ph st B ⇒ Term ph st (A `⇒ B) ]

  -- Action of thinnings on terms
  weak-Term : Γ ≤ Δ → Term ph st A Γ → Term ph st A Δ
  weak-Term σ (`var v) = `var (weak-Var σ v)
  weak-Term σ (`app f t) = `app (weak-Term σ f) (weak-Term σ t)
  weak-Term σ (`lam b) = `lam (weak-Term (keep σ) b)

  ----------------------------------------------------------------------
  -- Example of programs

  -- Phase-polymorphic but purely dynamic identity function
  `idᵈ : Term ph dynamic (A `⇒ A) ε
  `idᵈ = `lam (`var here)

  -- Stage-polymorphic function composition
  infixr 3 _`∘_
  _`∘_ : ∀[ Term ph st (B `⇒ C) ⇒ Term ph st (A `⇒ B) ⇒ Term ph st (A `⇒ C) ]
  g `∘ f = let Γ≤Γ,A = drop ≤-refl in
           `lam (`app (weak-Term Γ≤Γ,A g) (`app (weak-Term Γ≤Γ,A f) (`var here)))

  ----------------------------------------------------------------------
  -- Definition of the domain for staging by evaluation

  -- A domain for static values
  Static : Type static → Context → Set

  -- Static values are intepreted in the Static domain,
  -- Dynamic ones will become staged terms
  Value : (st : Stage source) → Type st → Context → Set
  Value static   = Static
  Value dynamic  = Term staged dynamic ∘ asStaged

  -- This is a fairly standard Kripke domain except that we
  -- cannot possibly have static neutral terms.
  Static `α        = const ⊥
  Static (A `⇒ B)  = Kripke (Static A) (Static B)

  -- Action of thinnings on Static
  weak-Static : (A : Type _) → Γ ≤ Δ → Static A Γ → Static A Δ
  weak-Static `α       σ = id
  weak-Static (A `⇒ B) σ = weak-Kripke σ

  -- Action of thinnings on Values
  weak-Value : (A : Type st) → Γ ≤ Δ → Value st A Γ → Value st A Δ
  weak-Value {st = static}  A σ v = weak-Static A σ v
  weak-Value {st = dynamic} A σ v = weak-Term σ v

  ------------------------------------------------------------------------
  -- Semantic counterparts to the language's constructs

  -- Semantics counterpart to app
  app : ∀ st {A B} → Value st (A `⇒ B) Γ → Value st A Γ → Value st B Γ
  app static   = _$$_
  app dynamic  = `app

  -- Semantics counterpart to λ-abstraction
  lam : (st : Stage source) {A B : Type st} →
        Kripke (Value st A) (Value st B) Γ →
        Value st (A `⇒ B) Γ
  lam static   b = λλ[ σ , v ] b .runBox σ v
  lam dynamic  b = `lam (b .runBox (drop ≤-refl) (`var here))






  ----------------------------------------------------------------------
  -- Adding quotes and splices
  ----------------------------------------------------------------------

  -- (⇑ A) is the static representation of a dynamic type A; that is
  -- to say it is morally the type of metaprograms returning code of
  -- type A. It may only be used in source terms.

  data Type where
    `⇑_   : Type {source} dynamic → Type static

  data Term where
    `⟨_⟩   : ∀[ Term source dynamic A ⇒ Term source static (`⇑ A) ]
    `∼_    : ∀[ Term source static (`⇑ A) ⇒ Term source dynamic A ]

  weak-Term σ `⟨ t ⟩ = `⟨ weak-Term σ t ⟩
  weak-Term σ (`∼ t) = `∼ weak-Term σ t

  ------------------------------------------------------------------------
  -- Example of programs

  -- Static identity function
  `idˢ : Term source static (A `⇒ A) ε
  `idˢ = `lam (`var here)

  ------------------------------------------------------------------------
  -- Definition of the domain for staging by evaluation

  -- Static metaprograms computing a term of type A are interpreted as
  -- dynamic values of type A i.e. staged terms of type A
  Static (`⇑ A) = Value dynamic A
  weak-Static (`⇑ A) σ = weak-Term σ






  ----------------------------------------------------------------------
  -- Adding natural numbers
  ----------------------------------------------------------------------

  data Type where
    `ℕ    : Type st

  asStaged `ℕ = `ℕ

  data Term where
    `zero  : ∀[ Term ph st `ℕ ]
    `succ  : ∀[ Term ph st `ℕ ⇒ Term ph st `ℕ ]
    `iter  : ∀[ Term ph st (`ℕ `⇒ (A `⇒ A) `⇒ A `⇒ A) ]

  weak-Term σ `zero = `zero
  weak-Term σ (`succ n) = `succ (weak-Term σ n)
  weak-Term σ `iter = `iter

  ------------------------------------------------------------------------
  -- Example of programs

  -- Turning static nats into dyanmic ones by computing their
  -- representation as codes
  `reify : ∀[ Term source static (`ℕ `⇒ `⇑ `ℕ) ]
  `reify = `lam (`app (`app (`app `iter (`var here)) (`lam `⟨ `succ (`∼ `var here) ⟩)) `⟨ `zero ⟩)

  -- Addition in terms of iteration
  `add : ∀[ Term ph st (`ℕ `⇒ `ℕ `⇒ `ℕ) ]
  `add = `lam (`app (`app `iter (`var here)) (`lam (`succ (`var here))))

  -- Double as addition of a term with itself.
  -- Note that we return a *dynamic* value which will have been
  -- computed at staging time
  `double : Term source static (`ℕ `⇒ `⇑ `ℕ) ε
  `double = `lam (`app `reify (`app (`app `add (`var here)) (`var here)))

  ------------------------------------------------------------------------
  -- Definition of the domain for staging by evaluation

  -- Static natural numbers are bona fide natural numbers
  Static `ℕ = const ℕ
  weak-Static `ℕ σ = id

  ------------------------------------------------------------------------
  -- Semantic counterparts to the language's constructs

  -- Semantics counterpart to zero
  zero : (st : Stage source) → Value st `ℕ Γ
  zero static   = 0
  zero dynamic  = `zero

  -- Semantics counterpart to succ
  succ : (st : Stage source) → Value st `ℕ Γ → Value st `ℕ Γ
  succ static   = 1 +_
  succ dynamic  = `succ

  -- Semantics counterpart to iter
  iterate : {ty : Set} → (ty → ty) → ty → ℕ → ty
  iterate succ zero 0        = zero
  iterate succ zero (suc n)  = succ (iterate succ zero n)

  iter : ∀ st {A} → Value st (`ℕ `⇒ (A `⇒ A) `⇒ (A `⇒ A)) Γ
  iter dynamic  = `iter
  iter static   = λλ[ _ , m ] λλ[ _ , succ ] λλ[ σ , zero ]
                  iterate (weak-Kripke σ succ $$_) zero m






  ----------------------------------------------------------------------
  -- Adding static pairs
  ----------------------------------------------------------------------

  -- Pairs are only for static data. This is a feature of 2 level TT
  -- that was already highlighted in András' paper: the two levels do
  -- not need to have the same features!
  data Type where
    _`×_  : (A B : Type static) → Type static

  data Term where
    _`,_   : ∀[ Term source static A ⇒ Term source static B ⇒ Term source static (A `× B) ]
    `fst   : ∀[ Term source static ((A `× B) `⇒ A) ]
    `snd   : ∀[ Term source static ((A `× B) `⇒ B) ]

  weak-Term σ (s `, t) = weak-Term σ s `, weak-Term σ t
  weak-Term σ `fst = `fst
  weak-Term σ `snd = `snd

  ------------------------------------------------------------------------
  -- Example of programs

  -- Efficiently computing the Fibonacci sequence using a pair
  -- of values. aux(n) = (fib n, fib (suc n))

  `fib : Term source static (`ℕ `⇒ `ℕ) ε
  `fib = `fst `∘ `lam (`app (`app (`app
    -- this implements n ↦ (fib n, fib (1 + n))
    `iter (`var here))
          {- step -} (`lam
            let fibₙ    = `app `fst (`var here)
                fib₁₊ₙ  = `app `snd (`var here)
                fib₂₊ₙ  = `app (`app `add fibₙ) fib₁₊ₙ
            in (fib₁₊ₙ `, fib₂₊ₙ)))
          {- base -} (`zero `, `succ `zero))


  Static (A `× B)  = Static A ∩ Static B
  weak-Static (A `× B) σ = Prod.map (weak-Static A σ) (weak-Static B σ)







------------------------------------------------------------------------
-- Evaluation function and staging corollary

-- Type of environments mapping variables to values
record Env (Γ Δ : Context) : Set where
  field lookup : ∀ {st A} → Var A Γ → Value st A Δ
open Env

-- Action of thinnings on environments
-- (pointwise lifting of the action on values)
weak-Env : Δ ≤ θ → Env Γ Δ → Env Γ θ
weak-Env σ ρ .lookup {A = A} v = weak-Value A σ (ρ .lookup v)

-- Extending an environment with a value to push it under a binder
extend : ∀[ Env Γ ⇒ □ (Value st A ⇒ Env (Γ , A)) ]
extend ρ .runBox σ v .lookup here = v
extend ρ .runBox σ v .lookup (there {A = B} x) = weak-Value B σ (ρ .lookup x)

-- `eval` and `body` are mutually defined.

-- `eval` turns source terms into values provided that we have
-- an environment assigning values to variables

-- `body` turns source terms defined in a context extended with
-- a fresh variable into kripke function spaces provided that we
-- have an environment for the original context

body : Env Γ Δ → Term source st B (Γ , A) →
       Kripke (Value st A) (Value st B) Δ

eval : Env Γ Δ → Term source st A Γ → Value st A Δ

eval ρ (`var v)              = ρ .lookup v
eval ρ (`app {st = st} f t)  = app st (eval ρ f) (eval ρ t)
eval ρ (`lam {st = st} b)    = lam st (body ρ b)
eval ρ (`zero {st = st})     = zero st
eval ρ (`succ {st = st} n)   = succ st (eval ρ n)
eval ρ (`iter {st = st})     = iter st
eval ρ `⟨ t ⟩                = eval ρ t
eval ρ (`∼ v)                = eval ρ v
eval ρ (s `, t)              = eval ρ s , eval ρ t
eval ρ `fst                  = λλ[ _ , v ] Prod.proj₁ v
eval ρ `snd                  = λλ[ _ , v ] Prod.proj₂ v

body ρ b = λλ[ σ , v ] eval (extend ρ .runBox σ v) b

-- Special case of evaluation: turning source terms into staged ones

stage : Term source dynamic A ε → Term staged dynamic (asStaged A) ε
stage = eval (λ where .lookup ())

open import Relation.Binary.PropositionalEquality using (_≡_; refl)




------------------------------------------------------------------------
-- Tests for the staging evaluator
------------------------------------------------------------------------

infix 0 _∋_↝_
_∋_↝_ : (A : Type dynamic) → Term source dynamic A ε → Term staged dynamic (asStaged A) ε → Set
A ∋ s ↝ t = stage s ≡ t

-- `idˢ is a static identity and thus computes
test-idˢ : `ℕ ∋ `∼ `app `idˢ `⟨ `zero ⟩ ↝ `zero
test-idˢ = refl

-- `idᵈ is a dynamic identity and thus stays stuck
test-idᵈ : `ℕ ∋ `app `idᵈ `zero ↝ `app `idᵈ `zero
test-idᵈ = refl

-- We can of course mix the two
test-idᵈˢ : stage (`app `idᵈ (`∼ `app `idˢ `⟨ `zero ⟩))
          ≡ `app `idᵈ `zero
test-idᵈˢ = refl

-- Just for ease of use in the test cases involving computations
fromℕ : ℕ → ∀[ Term ph st `ℕ ]
fromℕ ℕ.zero    = `zero
fromℕ (ℕ.suc n) = `succ (fromℕ n)

-- Finally, the static `double computes at staging time
test-double : `ℕ ∋ `∼ (`app `double (fromℕ 4)) ↝ fromℕ 8
test-double = refl

-- And computing fib by using pairs, a feature not available
-- in the target language!
test-fib :
  `ℕ ∋  `app (`app `add `zero) (`∼ `app (`reify `∘ `fib) (fromℕ 8))
     ↝  `app (`app `add `zero) (fromℕ 21)
test-fib = refl
