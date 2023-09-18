\begin{code}
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

open import Data.Bool.Base using (Bool; true; false)
open import Function.Base using (_∘_; id; const)
open import Relation.Unary using (IUniversal; _⇒_; _⊢_; _∩_)

------------------------------------------------------------------------
-- We have two stages: static and dynamic

\end{code}
%<*stage>
\begin{code}
data Stage : Set where
  static dynamic : Stage
\end{code}
%</stage>

%<*stagevariables>
\begin{code}
variable st a b : Stage
\end{code}
%</stagevariables>

\begin{code}
------------------------------------------------------------------------
-- Types are indexed by the stage they are defined at
--
-- (⇑ A) is the static representation of a dynamic type A; that is
-- to say it is morally the type of metaprograms returning code of
-- type A.
--
-- Function types are homogeneous: both domains and codomains need to
-- live at the same stage.
--
-- Pairs are only for static data. This is a feature of 2 level TT
-- that was already highlighted in András' paper: the two levels do
-- not need to have the same features!

infixr 10 _`×_
infixr 5 _`⇒_

\end{code}
%<*types>
\begin{code}
data Type : Stage → Set where
  `ℕ    : Type st
  `⇑_   : Type dynamic → Type static
  _`⇒_  : (A B : Type st) → Type st
  _`×_  : (A B : Type static) → Type static
\end{code}
%</types>
\begin{code}

variable
  A : Type a
  B : Type b

------------------------------------------------------------------------
-- Context are your usual left-nested lists of types.
-- Note the existential quantification over the stage of the freshly
-- bound variable in the snoc case

infixr 5 _-,_

\end{code}
%<*context>
\begin{code}
data Context : Set where
  ε     : Context
  _-,_  : Context → Type st → Context
\end{code}
%</context>
\begin{code}

variable
  Γ Δ θ : Context

------------------------------------------------------------------------
-- Thinnings

infix 0 _≤_

\end{code}
%<*thin>
\begin{code}
data _≤_ : Context → Context → Set where
  done  : ε ≤ ε
  keep  : Γ ≤ Δ → Γ -, A ≤ Δ -, A
  drop  : Γ ≤ Δ → Γ ≤ Δ -, A
\end{code}
%</thin>
\begin{code}

≤-trans : Γ ≤ Δ → Δ ≤ θ → Γ ≤ θ
≤-trans p (drop q) = drop (≤-trans p q)
≤-trans done done = done
≤-trans (keep p) (keep q) = keep (≤-trans p q)
≤-trans (drop p) (keep q) = drop (≤-trans p q)

\end{code}
%<*thinrefl>
\begin{code}
≤-refl : ∀ {Γ} → Γ ≤ Γ
≤-refl {ε} = done
≤-refl {Γ -, x} = keep ≤-refl
\end{code}
%</thinrefl>
\begin{code}

------------------------------------------------------------------------
-- Variables (could be defined as thinning from a singleton list)

\end{code}
%<*var>
\begin{code}
data Var : Type st → Context → Set where
  here   : ∀[          (_-, A) ⊢ Var A ]
  there  : ∀[ Var A ⇒  (_-, B) ⊢ Var A ]
\end{code}
%</var>
\begin{code}

weak-Var : Γ ≤ Δ → Var A Γ → Var A Δ
weak-Var (drop σ) v = there (weak-Var σ v)
weak-Var (keep σ) here = here
weak-Var (keep σ) (there v) = there (weak-Var σ v)

------------------------------------------------------------------------
-- Terms are indexed both by the stage of the type of the computation
-- they describe but also by a boolean describing whether it is legal
-- to uses quotes and splices

variable
  stg : Bool

\end{code}
%<*term>
\begin{code}
data Term : Bool → ∀ st → Type st → Context → Set where
  `var   : ∀[ Var A ⇒ Term stg st A ]
  `app   : ∀[ Term stg st (A `⇒ B) ⇒ Term stg st A ⇒ Term stg st B ]
  `lam   : ∀[ (_-, A) ⊢ Term stg st B ⇒ Term stg st (A `⇒ B) ]
  `zero  : ∀[ Term stg st `ℕ ]
  `succ  : ∀[ Term stg st `ℕ ⇒ Term stg st `ℕ ]
  `iter  : ∀[ Term stg st (`ℕ `⇒ (A `⇒ A) `⇒ A `⇒ A) ]
  `⟨_⟩   : ∀[ Term true _ A ⇒ Term true _ (`⇑ A) ]
  `∼_    : ∀[ Term true _ (`⇑ A) ⇒ Term true _ A ]
  _`,_   : ∀[ Term true _ A ⇒ Term true _ B ⇒ Term true _ (A `× B) ]
  `fst   : ∀[ Term true _ ((A `× B) `⇒ A) ]
  `snd   : ∀[ Term true _ ((A `× B) `⇒ B) ]
\end{code}
%</term>
\begin{code}

-- Action of thinnings on terms
weak-Term : Γ ≤ Δ → Term stg st A Γ → Term stg st A Δ
weak-Term σ (`var v) = `var (weak-Var σ v)
weak-Term σ (`app f t) = `app (weak-Term σ f) (weak-Term σ t)
weak-Term σ (`lam b) = `lam (weak-Term (keep σ) b)
weak-Term σ `zero = `zero
weak-Term σ (`succ n) = `succ (weak-Term σ n)
weak-Term σ `iter = `iter
weak-Term σ `⟨ t ⟩ = `⟨ weak-Term σ t ⟩
weak-Term σ (`∼ t) = `∼ weak-Term σ t
weak-Term σ (s `, t) = weak-Term σ s `, weak-Term σ t
weak-Term σ `fst = `fst
weak-Term σ `snd = `snd

------------------------------------------------------------------------
-- Source programs can use quotes and splices but staged code cannot

\end{code}
%<*termaliases>
\begin{code}
Source : ∀ st → Type st → Context → Set
Source = Term true

Staged : ∀ st → Type st → Context → Set
Staged = Term false
\end{code}
%</termaliases>
\begin{code}

------------------------------------------------------------------------
-- Example of programs

-- Purely dynamic identity function
\end{code}
%<*iddyn>
\begin{code}
`id₀ : Source dynamic (A `⇒ A) ε
`id₀ = `lam (`var here)
\end{code}
%</iddyn>
\begin{code}

-- Static identity function for dynamic values
\end{code}
%<*idsta>
\begin{code}
`id₁ : Source static (`⇑ A `⇒ `⇑ A) ε
`id₁ = `lam (`var here)
\end{code}
%</idsta>
\begin{code}

-- Turning static nats into dyanmic ones by computing their
-- representation as codes
\end{code}
\begin{code}
`reify : ∀[ Source static (`ℕ `⇒ `⇑ `ℕ) ]
`reify = `lam (`app (`app (`app `iter (`var here)) (`lam `⟨ `succ (`∼ `var here) ⟩)) `⟨ `zero ⟩)

-- Addition in terms of iteration
`add : ∀[ Source st (`ℕ `⇒ `ℕ `⇒ `ℕ) ]
`add = `lam (`app (`app `iter (`var here)) (`lam (`succ (`var here))))

-- Double as addition of a term with itself.
-- Note that we return a *dynamic* value which will have been
-- computed at staging time
`double : Source static (`ℕ `⇒ `⇑ `ℕ) ε
`double = `lam (`app `reify (`app (`app `add (`var here)) (`var here)))

-- Efficiently computing the Fibonacci sequence using a pair
-- of values. aux(n) = (fib n, fib (suc n))
-- Note that we return a dynamic value: the pairs will all be computed
-- away during staging!
`fib : Source static (`ℕ `⇒ `⇑ `ℕ) ε
`fib = `lam (`app `reify (`app `fst (`app aux (`var here)))) where

  aux : ∀[ Source static (`ℕ `⇒ `ℕ `× `ℕ) ]
  aux = `lam (`app (`app (`app `iter (`var here))
        {- step -} (`lam
          let fibn = `app `fst (`var here)
              fibsn = `app `snd (`var here)
          in fibsn `, `app (`app `add fibn) fibsn))
        {- base -} (`zero `, `succ `zero))

------------------------------------------------------------------------
-- Semantics toolkit: Kripke function spaces between
-- context-indexed type families

\end{code}
%<*kripke>
\begin{code}
record □ (A : Context → Set) (Γ : Context) : Set where
  constructor mkBox
  field runBox : ∀ {Δ} → Γ ≤ Δ → A Δ

Kripke : (A B : Context → Set) (Γ : Context) → Set
Kripke A B = □ (A ⇒ B)
\end{code}
%</kripke>
\begin{code}
open □

-- Action of thinnings on Kripke functions spaces
-- By construction they're the Free thinnable
weak-Kripke : ∀ {A B} → Γ ≤ Δ → Kripke A B Γ → Kripke A B Δ
weak-Kripke σ f .runBox = f .runBox ∘ ≤-trans σ

-- lambda-abstraction
infixr 3 mkBox
syntax mkBox (λ σ x → b) = λλ[ σ , x ] b

-- application
\end{code}
%<*kripkeapp>
\begin{code}
_$$_ : ∀ {A B} → Kripke A B Γ → A Γ → B Γ
f $$ t = f .runBox ≤-refl t
\end{code}
%</kripkeapp>
\begin{code}

------------------------------------------------------------------------
-- Definition of the domain for staging by evaluation

open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product as Prod using (_×_; _,_)

\end{code}
%<*modelstadecl>
\begin{code}
Static : Type static → Context → Set
\end{code}
%</modelstadecl>
\begin{code}

-- Static values are intepreted in the domain,
-- Dynamic ones will become staged terms
\end{code}
%<*model>
\begin{code}
Value : (st : Stage) → Type st → Context → Set
Value static   = Static
Value dynamic  = Staged dynamic
\end{code}
%</model>
\begin{code}

-- This is a fairly standard Kripke domain
\end{code}
%<*modelsta>
\begin{code}
Static `ℕ        = const ℕ
Static (`⇑ A)    = Value dynamic A
Static (A `⇒ B)  = Kripke (Static A) (Static B)
Static (A `× B)  = Static A ∩ Static B
\end{code}
%</modelsta>
\begin{code}

-- Action of thinnings on Kripke domains
weak-Static : (A : Type _) → Γ ≤ Δ → Static A Γ → Static A Δ
weak-Static `ℕ       σ = id
weak-Static (`⇑ A)   σ = weak-Term σ
weak-Static (A `⇒ B) σ = weak-Kripke σ
weak-Static (A `× B) σ = Prod.map (weak-Static A σ) (weak-Static B σ)

-- Action of thinnings on Values
weak-Value : (A : Type st) → Γ ≤ Δ → Value st A Γ → Value st A Δ
weak-Value {st = static}  A σ v = weak-Static A σ v
weak-Value {st = dynamic} A σ v = weak-Term σ v

------------------------------------------------------------------------
-- Evaluator for staging by evaluation

-- Type of environments mapping variables to values
record Env (Γ Δ : Context) : Set where
  field lookup : ∀ {st A} → Var A Γ → Value st A Δ
open Env

-- Action of thinnings on environments
-- (pointwise lifting of the action on values)
weak-Env : Δ ≤ θ → Env Γ Δ → Env Γ θ
weak-Env σ ρ .lookup {A = A} v = weak-Value A σ (ρ .lookup v)

-- Semantics counterpart to iter
iter : ∀ st {A} → Value st (`ℕ `⇒ (A `⇒ A) `⇒ (A `⇒ A)) Γ
iter dynamic = `iter
iter static {A}
  = λλ[ _ , m ] λλ[ _ , succ ] λλ[ σ , zero ]
    go A m (weak-Kripke σ succ) zero

  where

  go : (A : Type static) → (n : ℕ) →
       (succ : Kripke (Static A) (Static A) Γ) →
       (zero : Static A Γ) → Static A Γ
  go A ℕ.zero    succ zero = zero
  go A (ℕ.suc n) succ zero = succ $$ go A n succ zero

-- Semantics counterpart to app
\end{code}
%<*app>
\begin{code}
app : ∀ st {A B} → Value st (A `⇒ B) Γ → Value st A Γ → Value st B Γ
app static   f t = f $$ t
app dynamic  f t = `app f t
\end{code}
%</app>
\begin{code}

-- Extending an environment with a value to push it under a binder
\end{code}
%<*extend>
\begin{code}
extend : ∀[ Env Γ ⇒ □ (Value st A ⇒ Env (Γ -, A)) ]
extend ρ .runBox σ v .lookup here = v
extend ρ .runBox σ v .lookup (there {A = B} x) = weak-Value B σ (ρ .lookup x)

\end{code}
%</extend>
\begin{code}

\end{code}
%<*lam>
\begin{code}
lam : (st : Stage) {A B : Type st} →
      Kripke (Value st A) (Value st B) Γ →
      Value st (A `⇒ B) Γ
lam static   b = λλ[ σ , v ] b .runBox σ v
lam dynamic  b = `lam (b .runBox (drop ≤-refl) (`var here))
\end{code}
%</lam>
\begin{code}

-- Semantics counterpart to zero
\end{code}
%<*zero>
\begin{code}
zero : (st : Stage) → Value st `ℕ Γ
zero static   = ℕ.zero
zero dynamic  = `zero
\end{code}
%</zero>
\begin{code}

-- Semantics counterpart to succ
\end{code}
%<*succ>
\begin{code}
succ : (st : Stage) → Value st `ℕ Γ → Value st `ℕ Γ
succ static   = ℕ.suc
succ dynamic  = `succ
\end{code}
%</succ>

%<*bodydecl>
\begin{code}
body : Env Γ Δ → Source st B (Γ -, A) →
       Kripke (Value st A) (Value st B) Δ
\end{code}
%</bodydecl>
\begin{code}

-- Evaluation function turning source terms into values provided
-- we have an environment assigning values to variables
\end{code}
%<*evaldecl>
\begin{code}
eval : Env Γ Δ → Source st A Γ → Value st A Δ
\end{code}
%</evaldecl>
%<*eval>
\begin{code}
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
\end{code}
%</eval>

%<*body>
\begin{code}
body ρ b = λλ[ σ , v ] eval (extend ρ .runBox σ v) b
\end{code}
%</body>
\begin{code}

-- Special case of evaluation: turning source terms into staged ones

\end{code}
%<*stagedecl>
\begin{code}
stage : Source dynamic A ε → Staged dynamic A ε
\end{code}
%</stagedecl>
\begin{code}
stage = eval (λ where .lookup ())

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Tests for the staging evaluator

-- `id₁ is a static identity and thus computes
test-id₁ : stage (`∼ `app `id₁ `⟨ `zero ⟩) ≡ `zero
test-id₁ = refl

-- `id₀ is a dynamic identity and thus stays stuck
test-id₀ : stage (`app `id₀ `zero)
         ≡ `app (`lam (`var here)) `zero
test-id₀ = refl

-- We can of course mix the two
test-id₀₁ : stage (`app `id₀ (`∼ `app `id₁ `⟨ `zero ⟩))
          ≡ `app (`lam (`var here)) `zero
test-id₀₁ = refl

-- Just for ease of use in the test cases involving computations
fromℕ : ℕ → ∀[ Term stg st `ℕ ]
fromℕ ℕ.zero    = `zero
fromℕ (ℕ.suc n) = `succ (fromℕ n)

-- Finally, the static `double computes at staging time
test-double : stage (`∼ (`app `double (fromℕ 4))) ≡ fromℕ 8
test-double = refl

-- And computing fib by using pairs, a feature not available
-- in the target language!
test-fib : stage (`∼ (`app `fib (fromℕ 8))) ≡ fromℕ 21
test-fib = refl
