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

open import Function.Base using (_∘_; id; const)
open import Relation.Unary using (IUniversal; _⇒_; _⊢_; _∩_)

------------------------------------------------------------------------
-- We have two phases: source code and staged code

\end{code}
%<*phase>
\begin{code}
data Phase : Set where
  source staged : Phase

variable ph : Phase
\end{code}
%</phase>

\begin{code}

------------------------------------------------------------------------
-- We have two stages: static and dynamic

\end{code}
%<*stage>
\begin{code}
data Stage : Phase → Set where
  static : Stage source
  dynamic : Stage ph
\end{code}
%</stage>

%<*stagevariables>
\begin{code}
variable st : Stage ph
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
data Type : Stage ph → Set where
  `α    : Type st
\end{code}
%<*typesnat>
\begin{code}
  `ℕ    : Type st
\end{code}
%</typesnat>
\begin{code}
  `⇑_   : Type {source} dynamic → Type static
  _`⇒_  : (A B : Type st) → Type st
\end{code}
%<*typesprod>
\begin{code}
  _`×_  : (A B : Type static) → Type static
\end{code}
%</typesprod>
\begin{code}
\end{code}
%</types>
\begin{code}

variable
  A : Type st
  B : Type st
  C : Type st

\end{code}
%<*asStaged>
\begin{code}
asStaged : Type {source} dynamic → Type {staged} dynamic
asStaged `α        = `α
asStaged `ℕ        = `ℕ
asStaged (A `⇒ B)  = asStaged A `⇒ asStaged B
\end{code}
%</asStaged>
\begin{code}

------------------------------------------------------------------------
-- Context are your usual left-nested lists of types.
-- Note the existential quantification over the stage of the freshly
-- bound variable in the snoc case

infixl 4 _,_

\end{code}
%<*context>
\begin{code}
data Context : Set where
  ε    : Context
  _,_  : Context → Type st → Context
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
  keep  : Γ ≤ Δ → Γ , A ≤ Δ , A
  drop  : Γ ≤ Δ → Γ ≤ Δ , A
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
≤-refl {Γ , x} = keep ≤-refl
\end{code}
%</thinrefl>
\begin{code}

------------------------------------------------------------------------
-- Variables (could be defined as thinning from a singleton list)

\end{code}
%<*var>
\begin{code}
data Var : Type st → Context → Set where
  here   : ∀[          (_, A) ⊢ Var A ]
  there  : ∀[ Var A ⇒  (_, B) ⊢ Var A ]
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

\end{code}
%<*term>
\begin{code}
data Term : (ph : Phase) → (st : Stage ph) → Type st → Context → Set where
  `var   : ∀[ Var A ⇒ Term ph st A ]
  `app   : ∀[ Term ph st (A `⇒ B) ⇒ Term ph st A ⇒ Term ph st B ]
  `lam   : ∀[ (_, A) ⊢ Term ph st B ⇒ Term ph st (A `⇒ B) ]
\end{code}
%<*termnat>
\begin{code}
  `zero  : ∀[ Term ph st `ℕ ]
  `succ  : ∀[ Term ph st `ℕ ⇒ Term ph st `ℕ ]
  `iter  : ∀[ Term ph st (`ℕ `⇒ (A `⇒ A) `⇒ A `⇒ A) ]
\end{code}
%</termnat>
\begin{code}
  `⟨_⟩   : ∀[ Term source dynamic A ⇒ Term source static (`⇑ A) ]
  `∼_    : ∀[ Term source static (`⇑ A) ⇒ Term source dynamic A ]
\end{code}
%<*termprod>
\begin{code}
  _`,_   : ∀[ Term source static A ⇒ Term source static B ⇒ Term source static (A `× B) ]
  `fst   : ∀[ Term source static ((A `× B) `⇒ A) ]
  `snd   : ∀[ Term source static ((A `× B) `⇒ B) ]
\end{code}
%</termprod>
\begin{code}
\end{code}
%</term>
\begin{code}

-- Action of thinnings on terms
weak-Term : Γ ≤ Δ → Term ph st A Γ → Term ph st A Δ
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
-- Example of programs

-- Purely dynamic identity function
\end{code}
%<*iddyn>
\begin{code}
`idᵈ : Term ph dynamic (A `⇒ A) ε
`idᵈ = `lam (`var here)
\end{code}
%</iddyn>
\begin{code}

-- Static identity function
\end{code}
%<*idsta>
\begin{code}
`idˢ : Term source static (A `⇒ A) ε
`idˢ = `lam (`var here)
\end{code}
%</idsta>
\begin{code}

\end{code}
%<*composition>
\begin{code}
infixr 3 _`∘_
_`∘_ : ∀[ Term ph st (B `⇒ C) ⇒ Term ph st (A `⇒ B) ⇒ Term ph st (A `⇒ C) ]
g `∘ f =  let Γ≤Γ,A = drop ≤-refl in
          `lam (`app (weak-Term Γ≤Γ,A g) (`app (weak-Term Γ≤Γ,A f) (`var here)))
\end{code}
%</composition>
\begin{code}

-- Turning static nats into dyanmic ones by computing their
-- representation as codes
\end{code}
%<*reify>
\begin{code}
`reify : ∀[ Term source static (`ℕ `⇒ `⇑ `ℕ) ]
`reify = `lam (`app (`app (`app `iter (`var here)) (`lam `⟨ `succ (`∼ `var here) ⟩)) `⟨ `zero ⟩)
\end{code}
%</reify>
\begin{code}

-- Addition in terms of iteration
\end{code}
%<*add>
\begin{code}
`add : ∀[ Term ph st (`ℕ `⇒ `ℕ `⇒ `ℕ) ]
`add = `lam (`app (`app `iter (`var here)) (`lam (`succ (`var here))))
\end{code}
%</add>
\begin{code}

-- Double as addition of a term with itself.
-- Note that we return a *dynamic* value which will have been
-- computed at staging time
`double : Term source static (`ℕ `⇒ `⇑ `ℕ) ε
`double = `lam (`app `reify (`app (`app `add (`var here)) (`var here)))

-- Efficiently computing the Fibonacci sequence using a pair
-- of values. aux(n) = (fib n, fib (suc n))
\end{code}
%<*fib>
\begin{code}
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
\end{code}
%</fib>
\begin{code}

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

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; suc; _+_)
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
Value : (st : Stage source) → Type st → Context → Set
Value static   = Static
Value dynamic  = Term staged dynamic ∘ asStaged
\end{code}
%</model>
\begin{code}

-- This is a fairly standard Kripke domain
\end{code}
%<*modelsta>
\begin{code}
Static `α        = const ⊥
\end{code}
%<*modelnat>
\begin{code}
Static `ℕ        = const ℕ
\end{code}
%</modelnat>
\begin{code}
Static (`⇑ A)    = Value dynamic A
Static (A `⇒ B)  = Kripke (Static A) (Static B)
\end{code}
%<*modelprod>
\begin{code}
Static (A `× B)  = Static A ∩ Static B
\end{code}
%</modelprod>
%</modelsta>
\begin{code}

-- Action of thinnings on Kripke domains
weak-Static : (A : Type _) → Γ ≤ Δ → Static A Γ → Static A Δ
weak-Static `α       σ = id
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
\end{code}
%<*iter>
\begin{code}
iterate : {ty : Set} → (ty → ty) → ty → ℕ → ty
iterate succ zero 0        = zero
iterate succ zero (suc n)  = succ (iterate succ zero n)

iter : ∀ st {A} → Value st (`ℕ `⇒ (A `⇒ A) `⇒ (A `⇒ A)) Γ
iter dynamic  = `iter
iter static   = λλ[ _ , m ] λλ[ _ , succ ] λλ[ σ , zero ]
                iterate (weak-Kripke σ succ $$_) zero m
\end{code}
%</iter>
\begin{code}

-- Semantics counterpart to app
\end{code}
%<*app>
\begin{code}
app : ∀ st {A B} → Value st (A `⇒ B) Γ → Value st A Γ → Value st B Γ
app static   = _$$_
app dynamic  = `app
\end{code}
%</app>
\begin{code}

-- Extending an environment with a value to push it under a binder
\end{code}
%<*extend>
\begin{code}
extend : ∀[ Env Γ ⇒ □ (Value st A ⇒ Env (Γ , A)) ]
extend ρ .runBox σ v .lookup here = v
extend ρ .runBox σ v .lookup (there {A = B} x) = weak-Value B σ (ρ .lookup x)

\end{code}
%</extend>
\begin{code}

\end{code}
%<*lam>
\begin{code}
lam : (st : Stage source) {A B : Type st} →
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
zero : (st : Stage source) → Value st `ℕ Γ
zero static   = 0
zero dynamic  = `zero
\end{code}
%</zero>
\begin{code}

-- Semantics counterpart to succ
\end{code}
%<*succ>
\begin{code}
succ : (st : Stage source) → Value st `ℕ Γ → Value st `ℕ Γ
succ static   = 1 +_
succ dynamic  = `succ
\end{code}
%</succ>

%<*bodydecl>
\begin{code}
body : Env Γ Δ → Term source st B (Γ , A) →
       Kripke (Value st A) (Value st B) Δ
\end{code}
%</bodydecl>
\begin{code}

-- Evaluation function turning source terms into values provided
-- we have an environment assigning values to variables
\end{code}
%<*evaldecl>
\begin{code}
eval : Env Γ Δ → Term source st A Γ → Value st A Δ
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
\end{code}
%<*evalprod>
\begin{code}
eval ρ (s `, t)              = eval ρ s , eval ρ t
eval ρ `fst                  = λλ[ _ , v ] Prod.proj₁ v
eval ρ `snd                  = λλ[ _ , v ] Prod.proj₂ v
\end{code}
%</evalprod>
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
stage : Term source dynamic A ε → Term staged dynamic (asStaged A) ε
\end{code}
%</stagedecl>
\begin{code}
stage = eval (λ where .lookup ())

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Tests for the staging evaluator

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

test-add :
\end{code}
%<*testadd>
\begin{code}
  `ℕ ∋ `∼ `app `reify (`app (`app `add (fromℕ 7)) (fromℕ 35)) ↝ fromℕ 42
\end{code}
%</testadd>
\begin{code}
test-add = refl

-- Finally, the static `double computes at staging time
test-double : `ℕ ∋ `∼ (`app `double (fromℕ 4)) ↝ fromℕ 8
test-double = refl

-- And computing fib by using pairs, a feature not available
-- in the target language!
test-fib :
\end{code}
%<*testfib>
\begin{code}
  `ℕ ∋  `app (`app `add `zero) (`∼ `app (`reify `∘ `fib) (fromℕ 8))
     ↝  `app (`app `add `zero) (fromℕ 21)
\end{code}
%</testfib>
\begin{code}
test-fib = refl
