\begin{code}
{-# OPTIONS --safe --without-K #-}

module MetaCircuit where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Function.Base using (_∘_; id; const)
open import Relation.Unary using (IUniversal; _⇒_; _⊢_)

open import Agda.Builtin.FromNat
open import Data.Unit.Base
import Data.Nat.Literals; instance nat = Data.Nat.Literals.number
import Data.Fin.Literals; instance fin = λ {n} → Data.Fin.Literals.number n


data Phase : Set where
  source staged : Phase

variable ph : Phase

data Stage : Phase → Set where
  static   : Stage source
  dynamic  : Stage ph

variable st : Stage ph

infixr 3 _`⇒_
infixr 5 `⇑_

\end{code}
%<*type>
\begin{code}
data Type : ∀ {ph} → Stage ph → Set where
  _`⇒_   : (A B : Type static) → Type static
  `⇑_    : Type {source} dynamic → Type static
  ⟨_∶_⟩  : (i o : ℕ) → Type {ph} dynamic
\end{code}
%</type>
\begin{code}
  `Bool : Type static

variable m i o i₁ o₁ i₂ o₂ : ℕ
variable A B C : Type st

\end{code}
%<*asStaged>
\begin{code}
asStaged : Type {source} dynamic → Type {staged} dynamic
asStaged ⟨ i ∶ o ⟩ = ⟨ i ∶ o ⟩
\end{code}
%</asStaged>
\begin{code}

infixl 3 _,_
data Context : Set where
  ε    : Context
  _,_  : Context → Type st → Context

variable Γ Δ Θ : Context

infix 0 _≤_
data _≤_ : Context → Context → Set where
  done  : ε ≤ ε
  keep  : Γ ≤ Δ → Γ , A ≤ Δ , A
  drop  : Γ ≤ Δ → Γ ≤ Δ , A

≤-trans : Γ ≤ Δ → Δ ≤ Θ → Γ ≤ Θ
≤-trans p (drop q) = drop (≤-trans p q)
≤-trans done done = done
≤-trans (keep p) (keep q) = keep (≤-trans p q)
≤-trans (drop p) (keep q) = drop (≤-trans p q)

≤-refl : ∀ {Γ} → Γ ≤ Γ
≤-refl {ε} = done
≤-refl {Γ , x} = keep ≤-refl

data Var : Type st → Context → Set where
  here   : ∀[          (_, A) ⊢ Var A ]
  there  : ∀[ Var A ⇒  (_, B) ⊢ Var A ]

weak-Var : Γ ≤ Δ → Var A Γ → Var A Δ
weak-Var (drop σ) v = there (weak-Var σ v)
weak-Var (keep σ) here = here
weak-Var (keep σ) (there v) = there (weak-Var σ v)


data Term : (ph : Phase) (st : Stage ph) → Type st → Context → Set where
  -- stlc
  `var   : ∀[ Var A ⇒ Term ph st A ]
  `app   : ∀[ Term source static (A `⇒ B) ⇒ Term source static A ⇒ Term source static B ]
  `lam   : ∀[ (_, A) ⊢ Term source static B ⇒ Term source static (A `⇒ B) ]
  -- two level
  `⟨_⟩   : ∀[ Term source dynamic A ⇒ Term source static (`⇑ A) ]
  `∼_    : ∀[ Term source static (`⇑ A) ⇒ Term source dynamic A ]
  -- booleans
  `true   : ∀[ Term source static `Bool ]
  `false  : ∀[ Term source static `Bool ]
  `ifte   : ∀[ Term source static (`Bool `⇒ A `⇒ A `⇒ A) ]
  -- circuit
\end{code}
%<*termcircuit>
%<*termcircuitnand>
\begin{code}
  `nand  : ∀[ Term ph dynamic ⟨ 2 ∶ 1 ⟩ ]
\end{code}
%</termcircuitnand>
%<*termcircuitpar>
\begin{code}
  `par   : ∀[  Term ph dynamic ⟨ i₁ ∶ o₁ ⟩ ⇒
               Term ph dynamic ⟨ i₂ ∶ o₂ ⟩ ⇒
               Term ph dynamic ⟨ i₁ + i₂ ∶ o₁ + o₂ ⟩ ]
\end{code}
%</termcircuitpar>
%<*termcircuitseq>
\begin{code}
  `seq   : ∀[  Term ph dynamic ⟨ i ∶ m ⟩ ⇒
               Term ph dynamic ⟨ m ∶ o ⟩ ⇒
               Term ph dynamic ⟨ i ∶ o ⟩ ]
\end{code}
%</termcircuitseq>
%<*termcircuitmix>
\begin{code}
  `mix   : Vec (Fin i) o → ∀[ Term ph dynamic ⟨ i ∶ o ⟩ ]
\end{code}
%</termcircuitmix>

%<*id2>
\begin{code}
`id₂ :  ∀[ Term ph dynamic ⟨ 2 ∶ 2 ⟩ ]
`id₂ = `mix (zero ∷ suc zero ∷ [])
\end{code}
%</id2>

%<*swap>
\begin{code}
`swap :  ∀[ Term ph dynamic ⟨ 2 ∶ 2 ⟩ ]
`swap = `mix (suc zero ∷ zero ∷ [])
\end{code}
%</swap>

%<*dup>
\begin{code}
`dup :  ∀[ Term ph dynamic ⟨ 1 ∶ 2 ⟩ ]
`dup = `mix (zero ∷ zero ∷ [])
\end{code}
%</dup>

%<*diag>
\begin{code}
`diag : ∀[ Term source static (`⇑ ⟨ 2 ∶ 1 ⟩ `⇒ `⇑ ⟨ 1 ∶ 1 ⟩) ]
`diag = `lam `⟨ `seq `dup (`∼ `var here) ⟩
\end{code}
%</diag>

%<*not>
\begin{code}
`not : ∀[ Term source dynamic ⟨ 1 ∶ 1 ⟩ ]
`not = `∼ `app `diag `⟨ `nand ⟩
\end{code}
%</not>

\begin{code}
`and : ∀[ Term source dynamic ⟨ 2 ∶ 1 ⟩ ]
`and = `seq `nand `not

`or : ∀[ Term source dynamic ⟨ 2 ∶ 1 ⟩ ]
`or = `seq (`par `not `not) `nand

`id₁ : ∀[ Term ph dynamic ⟨ 1 ∶ 1 ⟩ ]
`id₁ = `mix (zero ∷ [])
\end{code}
%<*tab>
\begin{code}
`tab : ∀[ Term source static ((`Bool `⇒ `⇑ ⟨ 1 ∶ 1 ⟩) `⇒ `⇑ ⟨ 2 ∶ 1 ⟩) ]
`tab = `lam `⟨ `seq (`seq (`seq
         (`par `dup `dup)
         (`mix (0 ∷ 2 ∷ 1 ∷ 3 ∷ [])))
         (`par (`seq (`par `id₁ (`∼ `app (`var here) `true))  `and)
               (`seq (`par `not (`∼ `app (`var here) `false)) `and)))
         `or ⟩
\end{code}
%</tab>

\begin{code}
-- Action of thinnings on terms
weak-Term : Γ ≤ Δ → Term ph st A Γ → Term ph st A Δ
weak-Term σ (`var v) = `var (weak-Var σ v)
weak-Term σ (`app f t) = `app (weak-Term σ f) (weak-Term σ t)
weak-Term σ (`lam b) = `lam (weak-Term (keep σ) b)
weak-Term σ `⟨ t ⟩ = `⟨ weak-Term σ t ⟩
weak-Term σ (`∼ t) = `∼ weak-Term σ t
weak-Term σ `nand = `nand
weak-Term σ (`par s t) = `par (weak-Term σ s) (weak-Term σ t)
weak-Term σ (`seq s t) = `seq (weak-Term σ s) (weak-Term σ t)
weak-Term σ (`mix k) = `mix k
weak-Term σ `true = `true
weak-Term σ `false = `true
weak-Term σ `ifte = `ifte

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

weak-Kripke : ∀ {A B} → Γ ≤ Δ → Kripke A B Γ → Kripke A B Δ
weak-Kripke σ f .runBox = f .runBox ∘ ≤-trans σ

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
f $$ t = f .runBox ≤-refl t
\end{code}
%</kripkeapp>
\begin{code}

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
Static (`⇑ A)    = Value dynamic A
Static (A `⇒ B)  = Kripke (Static A) (Static B)
\end{code}
%</modelsta>
\begin{code}
Static `Bool     = const Bool

-- Action of thinnings on Kripke domains
weak-Static : (A : Type _) → Γ ≤ Δ → Static A Γ → Static A Δ
weak-Static (`⇑ A)   σ = weak-Term σ
weak-Static (A `⇒ B) σ = weak-Kripke σ
weak-Static `Bool    σ = id

-- Action of thinnings on Values
weak-Value : (A : Type st) → Γ ≤ Δ → Value st A Γ → Value st A Δ
weak-Value {st = static}  A σ v = weak-Static A σ v
weak-Value {st = dynamic} A σ v = weak-Term σ v

-- Type of environments mapping variables to values
record Env (Γ Δ : Context) : Set where
  field lookup : ∀ {st A} → Var A Γ → Value st A Δ
open Env

-- Action of thinnings on environments
-- (pointwise lifting of the action on values)
weak-Env : Δ ≤ Θ → Env Γ Δ → Env Γ Θ
weak-Env σ ρ .lookup {A = A} v = weak-Value A σ (ρ .lookup v)

-- Extending an environment with a value to push it under a binder
\end{code}
%<*extend>
\begin{code}
extend : ∀[ Env Γ ⇒ □ (Value st A ⇒ Env (Γ , A)) ]
extend ρ .runBox σ v .lookup here = v
extend ρ .runBox σ v .lookup (there {A = B} x) = weak-Value B σ (ρ .lookup x)
\end{code}
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
eval ρ (`var v)    = ρ .lookup v
eval ρ (`app f t)  = eval ρ f $$ eval ρ t
eval ρ (`lam b)    = body ρ b
eval ρ `⟨ t ⟩      = eval ρ t
eval ρ (`∼ v)      = eval ρ v
eval ρ `nand       = `nand
eval ρ (`par s t)  = `par (eval ρ s) (eval ρ t)
eval ρ (`seq s t)  = `seq (eval ρ s) (eval ρ t)
eval ρ (`mix k)    = `mix k
\end{code}
%</eval>
\begin{code}
eval ρ `true = true
eval ρ `false = false
eval ρ (`ifte {A = A})
  = λλ[ _ , b ] λλ[ _ , t ] λλ[ σ , f ]
    (if b then weak-Value A σ t else f)
\end{code}

%<*body>
\begin{code}
body ρ b = λλ[ σ , v ] eval (extend ρ .runBox σ v) b
\end{code}
%</body>
\begin{code}

-- Special case of evaluation: turning source terms into staged ones

\end{code}
%<*stagefun>
%<*stagedecl>
\begin{code}
stage : Term source dynamic A ε → Term staged dynamic (asStaged A) ε
\end{code}
%</stagedecl>
\begin{code}
stage = eval (λ where .lookup ())
\end{code}
%</stagefun>
\begin{code}


open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Tests for the staging evaluator

infix 0 _∋_↝_
_∋_↝_ : (A : Type dynamic) → Term source dynamic A ε → Term staged dynamic (asStaged A) ε → Set
A ∋ s ↝ t = stage s ≡ t

testNot :
\end{code}
%<*testNot>
\begin{code}
  ⟨ 1 ∶ 1 ⟩ ∋ `not ↝ `seq `dup `nand
\end{code}
%</testNot>
\begin{code}
testNot = refl


\end{code}
