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

-- This is the stripped down version with nothing but
-- quotes and splices! See TwoTT for a more reasonable
-- programming langauge.
module BasicTwoTT where

open import Data.Default
open import Data.Empty using (⊥)
open import Function.Base using (_∘_; id; const)
open import Relation.Unary using (IUniversal; _⇒_; _⊢_; _∩_)

------------------------------------------------------------------------
-- We have two phases: source code and staged code

\end{code}
%<*phase>
\begin{code}
data Phase : Set where
  src stg : Phase

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
  sta : Stage src
  dyn : Stage ph

variable st : Stage ph
\end{code}
%</stage>
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

infixr 5 _`⇒_

\end{code}
%<*types>
\begin{code}
data Type : Stage ph → Set where
  `α    : Type st
  _`⇒_  : (A B : Type st) → Type st
  `⇑_   : Type {src} dyn → Type sta

variable A B C : Type st
\end{code}
%</types>
\begin{code}

\end{code}
%<*asStaged>
\begin{code}
asStaged : Type {src} dyn → Type {stg} dyn
asStaged `α        = `α
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
  Γ Δ Θ : Context

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

≤-trans : Γ ≤ Δ → Δ ≤ Θ → Γ ≤ Θ
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
%<*termdecl>
\begin{code}
data Term : (ph : Phase) (st : Stage ph) →
            Type st → Context → Set where
\end{code}
%</termdecl>
%<*termstlc>
\begin{code}
  `var   : ∀[ Var A ⇒ Term ph st A ]
  `app   : ∀[ Term ph st (A `⇒ B) ⇒ Term ph st A ⇒ Term ph st B ]
  `lam   : ∀[ (_, A) ⊢ Term ph st B ⇒ Term ph st (A `⇒ B) ]
\end{code}
%</termstlc>
%<*termtwolevel>
\begin{code}
  `⟨_⟩   : ∀[ Term src dyn A ⇒ Term src sta (`⇑ A) ]
  `∼_    : ∀[ Term src sta (`⇑ A) ⇒ Term src dyn A ]
\end{code}
%</termtwolevel>
%</term>
\begin{code}

-- Action of thinnings on terms
weak-Term : Γ ≤ Δ → Term ph st A Γ → Term ph st A Δ
weak-Term σ (`var v) = `var (weak-Var σ v)
weak-Term σ (`app f t) = `app (weak-Term σ f) (weak-Term σ t)
weak-Term σ (`lam b) = `lam (weak-Term (keep σ) b)
weak-Term σ `⟨ t ⟩ = `⟨ weak-Term σ t ⟩
weak-Term σ (`∼ t) = `∼ weak-Term σ t

------------------------------------------------------------------------
-- Example of programs

open WithDefault

-- Purely dynamic identity function
\end{code}
%<*iddyn>
\begin{code}
`idᵈ : ∀[ Term ph dyn (A `⇒ A) ]
`idᵈ = `lam (`var here)
\end{code}
%</iddyn>
\begin{code}

-- Static identity function for dynamic values
\end{code}
%<*idsta>
\begin{code}
`idˢ : ∀[ Term src sta (A `⇒ A) ]
`idˢ = `lam (`var here)
\end{code}
%</idsta>
\begin{code}

infixr 3 _`∘_
\end{code}
%<*composition>
\begin{code}
_`∘_    : ∀[ Term ph st (B `⇒ C) ⇒ Term ph st (A `⇒ B) ⇒ Term ph st (A `⇒ C) ]
g `∘ f  =  let Γ≤Γ,A = drop ≤-refl in
           `lam (`app (weak-Term Γ≤Γ,A g) (`app (weak-Term Γ≤Γ,A f) (`var here)))
\end{code}
%</composition>
\begin{code}

------------------------------------------------------------------------
-- Semantics toolkit: Kripke function spaces between
-- context-indexed type families

\end{code}
%<*kripke>
\begin{code}
record □ (A : Context → Set) (Γ : Context) : Set where
  constructor mkBox
  field run□ : ∀ {Δ} → Γ ≤ Δ → A Δ

Kripke : (A B : Context → Set) (Γ : Context) → Set
Kripke A B = □ (A ⇒ B)
\end{code}
%</kripke>
\begin{code}
open □

-- Action of thinnings on Kripke functions spaces
-- By construction they're the Free thinnable
weak-Kripke : ∀ {A B} → Γ ≤ Δ → Kripke A B Γ → Kripke A B Δ
weak-Kripke σ f .run□ = f .run□ ∘ ≤-trans σ

-- lambda-abstraction
infixr 3 mkBox
\end{code}
%<*kripkelam>
\begin{code}
syntax mkBox (λ σ x → b) = λλ[ σ , x ] b
\end{code}
%</kripkelam>
\begin{code}

-- application
\end{code}
%<*kripkeapp>
\begin{code}
_$$_ : ∀ {A B} → Kripke A B Γ → A Γ → B Γ
f $$ t = f .run□ ≤-refl t
\end{code}
%</kripkeapp>
\begin{code}

------------------------------------------------------------------------
-- Definition of the domain for staging by evaluation

open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product as Prod using (_×_; _,_)

\end{code}
%<*modelstadecl>
\begin{code}
Static : Type sta → Context → Set
\end{code}
%</modelstadecl>
\begin{code}

-- Static values are intepreted in the domain,
-- Dynamic ones will become staged terms
\end{code}
%<*model>
\begin{code}
Value : (st : Stage src) → Type st → Context → Set
Value sta  = Static
Value dyn  = Term stg dyn ∘ asStaged
\end{code}
%</model>
\begin{code}

-- This is a fairly standard Kripke domain
\end{code}
%<*modelsta>
\begin{code}
Static `α        = const ⊥
Static (`⇑ A)    = Value dyn A
Static (A `⇒ B)  = Kripke (Static A) (Static B)
\end{code}
%</modelsta>
\begin{code}

-- Action of thinnings on Kripke domains
weak-Static : (A : Type _) → Γ ≤ Δ → Static A Γ → Static A Δ
weak-Static `α       σ = id
weak-Static (`⇑ A)   σ = weak-Term σ
weak-Static (A `⇒ B) σ = weak-Kripke σ

-- Action of thinnings on Values
weak-Value : (A : Type st) → Γ ≤ Δ → Value st A Γ → Value st A Δ
weak-Value {st = sta} A σ v = weak-Static A σ v
weak-Value {st = dyn} A σ v = weak-Term σ v

------------------------------------------------------------------------
-- Evaluator for staging by evaluation

-- Type of environments mapping variables to values
record Env (Γ Δ : Context) : Set where
  field get : ∀ {st A} → Var A Γ → Value st A Δ
open Env

-- Action of thinnings on environments
-- (pointwise lifting of the action on values)
weak-Env : Δ ≤ Θ → Env Γ Δ → Env Γ Θ
weak-Env σ ρ .get {A = A} v = weak-Value A σ (ρ .get v)

-- Semantics counterpart to app
\end{code}
%<*app>
\begin{code}
app : (st : Stage src) {A B : Type st} →
      Value st (A `⇒ B) Γ → Value st A Γ → Value st B Γ
app sta  = _$$_
app dyn  = `app
\end{code}
%</app>
\begin{code}

-- Extending an environment with a value to push it under a binder
\end{code}
%<*extend>
\begin{code}
extend : ∀[ Env Γ ⇒ □ (Value st A ⇒ Env (Γ , A)) ]
extend ρ .run□ σ v .get here = v
extend ρ .run□ σ v .get (there {A = B} x) = weak-Value B σ (ρ .get x)

\end{code}
%</extend>
\begin{code}

\end{code}
%<*lam>
\begin{code}
lam : (st : Stage src) {A B : Type st} →
      Kripke (Value st A) (Value st B) Γ →
      Value st (A `⇒ B) Γ
lam sta  b = λλ[ σ , v ] b .run□ σ v
lam dyn  b = `lam (b .run□ (drop ≤-refl) (`var here))
\end{code}
%</lam>

%<*bodydecl>
\begin{code}
body : Env Γ Δ → Term src st B (Γ , A) →
       Kripke (Value st A) (Value st B) Δ
\end{code}
%</bodydecl>
\begin{code}

-- Evaluation function turning source terms into values provided
-- we have an environment assigning values to variables
\end{code}
%<*evaldecl>
\begin{code}
eval : Env Γ Δ → Term src st A Γ → Value st A Δ
\end{code}
%</evaldecl>
%<*eval>
\begin{code}
eval ρ (`var v)              = ρ .get v
eval ρ (`app {st = st} f t)  = app st (eval ρ f) (eval ρ t)
eval ρ (`lam {st = st} b)    = lam st (body ρ b)
eval ρ `⟨ t ⟩                = eval ρ t
eval ρ (`∼ v)                = eval ρ v
\end{code}
%</eval>

%<*body>
\begin{code}
body ρ b = λλ[ σ , v ] eval (extend ρ .run□ σ v) b
\end{code}
%</body>
\begin{code}

-- Special case of evaluation: turning source terms into staged ones

\end{code}
%<*stagefun>
%<*stagedecl>
\begin{code}
stage : Term src dyn A ε → Term stg dyn (asStaged A) ε
\end{code}
%</stagedecl>
\begin{code}
stage = eval (λ where .get ())
\end{code}
%</stagefun>
\begin{code}

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Tests for the staging evaluator

infix 0 _∋_↝_
\end{code}
%<*stagedto>
\begin{code}
_∋_↝_ : (A : Type dyn) →
        Term src dyn A ε →
        Term stg dyn (asStaged A) ε → Set
A ∋ s ↝ t = stage s ≡ t
\end{code}
%</stagedto>
\begin{code}

-- `idˢ is a static identity and thus computes
\end{code}
%<*testid1>
\begin{code}
test-idˢ : `α `⇒ `α  ∋  `∼ `app `idˢ `⟨ `idᵈ ⟩
                     ↝  `idᵈ
test-idˢ = refl
\end{code}
%</testid1>
\begin{code}

-- `idᵈ is a dynamic identity and thus stays stuck
test-idᵈ : `α `⇒ `α  ∋  `app `idᵈ `idᵈ
                     ↝  `app `idᵈ `idᵈ
test-idᵈ = refl

-- We can mix the two!
test-idᵈˢ :
\end{code}
%<*testid01>
\begin{code}
  `α `⇒ `α  ∋  `app `idᵈ (`∼ `app `idˢ `⟨ `idᵈ ⟩) ↝  `app `idᵈ `idᵈ
\end{code}
%</testid01>
\begin{code}
test-idᵈˢ = refl
