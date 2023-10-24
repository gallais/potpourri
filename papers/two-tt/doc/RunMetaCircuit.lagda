\begin{code}
{-# OPTIONS --safe --without-K #-}

module RunMetaCircuit where

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_)
open import Data.Empty using (⊥)
open import Data.Fin.Base as Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product.Base using () renaming (_,_ to _,,_)
open import Data.Vec.Base as Vec using (Vec; []; _∷_; _++_; splitAt)
open import Function.Base using (_$_; _∘_; id; const)
open import Relation.Unary using (IUniversal; _⇒_; _⊢_)

open import Agda.Builtin.FromNat
open import Data.Unit.Base
import Data.Nat.Literals; instance nat = Data.Nat.Literals.number
import Data.Fin.Literals; instance fin = λ {n} → Data.Fin.Literals.number n

data Phase : Set where
  src stg : Phase

variable ph : Phase

data Stage : Phase → Set where
  sta : Stage src
  dyn : Stage ph

variable st : Stage ph

infixr 3 _`⇒_
infixr 5 `⇑_

\end{code}
%<*type>
\begin{code}
data Type : Stage ph → Set where
  _`⇒_    : (A B : Type sta) → Type sta
  `⇑_     : Type {src} dyn → Type sta
  `⟨_∣_⟩  : (i o : ℕ) → Type {ph} st
  `[_]    : (n : ℕ) → Type sta
\end{code}
%</type>
\begin{code}
  `Bool : Type sta

variable m n i o i₁ o₁ i₂ o₂ : ℕ
variable A B C : Type st

\end{code}
%<*asStaged>
\begin{code}
asStaged : Type {src} dyn → Type {stg} dyn
asStaged `⟨ i ∣ o ⟩ = `⟨ i ∣ o ⟩
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
  `app   : ∀[ Term src sta (A `⇒ B) ⇒ Term src sta A ⇒ Term src sta B ]
  `lam   : ∀[ (_, A) ⊢ Term src sta B ⇒ Term src sta (A `⇒ B) ]
  -- two level
  `⟨_⟩   : ∀[ Term src dyn A ⇒ Term src sta (`⇑ A) ]
  `∼_    : ∀[ Term src sta (`⇑ A) ⇒ Term src dyn A ]
  `run   : ∀[ Term src sta `⟨ i ∣ o ⟩ ⇒ Term src sta (`[ i ] `⇒ `[ o ]) ]
  `tab   : ∀[ Term src sta (`[ i ] `⇒ `[ o ]) ⇒ Term src st `⟨ i ∣ o ⟩ ]
  -- booleans
  `true   : ∀[ Term src sta `Bool ]
  `false  : ∀[ Term src sta `Bool ]
  `ifte   : ∀[ Term src sta (`Bool `⇒ A `⇒ A `⇒ A) ]
  -- vectors
  `nil    : ∀[ Term src sta `[ 0 ] ]
  `cons   : ∀[ Term src sta (`Bool `⇒ `[ n ] `⇒ `[ suc n ]) ]
  `split  : ∀[ Term src sta ((`Bool `⇒ `[ n ] `⇒ A) `⇒ `[ suc n ] `⇒ A) ]
  -- circuit
\end{code}
%<*termcircuit>
%<*termcircuitconstant>
\begin{code}
  `const : Bool → ∀[ Term ph dyn `⟨ 0 ∣ 1 ⟩ ]
\end{code}
%<*termcircuitnand>
\begin{code}
  `nand  : ∀[ Term ph dyn `⟨ 2 ∣ 1 ⟩ ]
\end{code}
%</termcircuitnand>
%<*termcircuitpar>
\begin{code}
  `par   : ∀[  Term ph dyn `⟨ i₁        ∣ o₁        ⟩ ⇒
               Term ph dyn `⟨       i₂  ∣       o₂  ⟩ ⇒
               Term ph dyn `⟨ i₁ +  i₂  ∣ o₁ +  o₂  ⟩ ]
\end{code}
%</termcircuitpar>
%<*termcircuitseq>
\begin{code}
  `seq   : ∀[  Term ph dyn `⟨ i  ∣ m  ⟩ ⇒
               Term ph dyn `⟨ m  ∣ o  ⟩ ⇒
               Term ph dyn `⟨ i  ∣ o  ⟩ ]
\end{code}
%</termcircuitseq>
%<*termcircuitmix>
\begin{code}
  `mix   : Vec (Fin i) o → ∀[ Term ph dyn `⟨ i ∣ o ⟩ ]
\end{code}
%</termcircuitmix>

%<*id2>
\begin{code}
`id₂ :  ∀[ Term ph dyn `⟨ 2 ∣ 2 ⟩ ]
`id₂ = `mix (0 ∷ 1 ∷ [])
\end{code}
%</id2>

%<*swap>
\begin{code}
`swap :  ∀[ Term ph dyn `⟨ 2 ∣ 2 ⟩ ]
`swap = `mix (1 ∷ 0 ∷ [])
\end{code}
%</swap>

%<*dup>
\begin{code}
`dup :  ∀[ Term ph dyn `⟨ 1 ∣ 2 ⟩ ]
`dup = `mix (0 ∷ 0 ∷ [])
\end{code}
%</dup>

%<*diag>
\begin{code}
`diag : ∀[ Term src sta (`⇑ `⟨ 2 ∣ 1 ⟩ `⇒ `⇑ `⟨ 1 ∣ 1 ⟩) ]
`diag = `lam `⟨ `seq `dup (`∼ `var here) ⟩
\end{code}
%</diag>

%<*not>
\begin{code}
`not : ∀[ Term ph dyn `⟨ 1 ∣ 1 ⟩ ]
`not = `seq `dup `nand
\end{code}
%</not>

%<*and>
\begin{code}
`and : ∀[ Term ph dyn `⟨ 2 ∣ 1 ⟩ ]
`and = `seq `nand `not
\end{code}
%</and>
\begin{code}

\end{code}
%<*or>
\begin{code}
`or : ∀[ Term ph dyn `⟨ 2 ∣ 1 ⟩ ]
`or = `seq (`par `not `not) `nand
\end{code}
%</or>
\begin{code}

`id₁ : ∀[ Term ph dyn `⟨ 1 ∣ 1 ⟩ ]
`id₁ = `mix (zero ∷ [])

-- Action of thinnings on terms
weak-Term : Γ ≤ Δ → Term ph st A Γ → Term ph st A Δ
weak-Term σ (`var v) = `var (weak-Var σ v)
weak-Term σ (`app f t) = `app (weak-Term σ f) (weak-Term σ t)
weak-Term σ (`lam b) = `lam (weak-Term (keep σ) b)
weak-Term σ `⟨ t ⟩ = `⟨ weak-Term σ t ⟩
weak-Term σ (`∼ t) = `∼ weak-Term σ t
weak-Term σ (`run t) = `run (weak-Term σ t)
weak-Term σ (`tab t) = `tab (weak-Term σ t)
weak-Term σ (`const b) = `const b
weak-Term σ `nand = `nand
weak-Term σ (`par s t) = `par (weak-Term σ s) (weak-Term σ t)
weak-Term σ (`seq s t) = `seq (weak-Term σ s) (weak-Term σ t)
weak-Term σ (`mix k) = `mix k
weak-Term σ `true = `true
weak-Term σ `false = `true
weak-Term σ `ifte = `ifte
weak-Term σ `nil = `nil
weak-Term σ `cons = `cons
weak-Term σ `split = `split

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
Static : Type sta → Set
\end{code}
%</modelstadecl>
\begin{code}

-- Static values are intepreted in the domain,
-- Dynamic ones will become staged terms
\end{code}
%<*model>
\begin{code}
Value : (st : Stage src) → Type st → Set
Value sta  A = Static A
Value dyn  A = Term stg dyn (asStaged A) ε
\end{code}
%</model>
\begin{code}

-- This is a fairly standard Kripke domain
\end{code}
%<*modelsta>
\begin{code}
Static (`⇑ A)      = Value dyn A
Static (A `⇒ B)    = Static A → Static B
\end{code}
%</modelsta>
\begin{code}
Static `⟨ i ∣ o ⟩  = Term stg dyn `⟨ i ∣ o ⟩ ε
Static `[ n ]      = Vec Bool n
Static `Bool       = Bool


-- Type of environments mapping variables to values
record Env (Γ : Context) : Set where
  field lookup : ∀ {st A} → Var A Γ → Value st A
open Env

-- Extending an environment with a value to push it under a binder
\end{code}
%<*extend>
\begin{code}
extend : Env Γ → Value st A → Env (Γ , A)
extend ρ v .lookup here = v
extend ρ v .lookup (there x) = ρ .lookup x
\end{code}
%<*bodydecl>
\begin{code}
body : Env Γ → Term src st B (Γ , A) →
       Value st A → Value st B
\end{code}
%</bodydecl>
\begin{code}

≈_ : Term stg dyn `⟨ i ∣ o ⟩ ε → Vec Bool i → Vec Bool o
(≈ `const b)  vs            = b ∷ []
(≈ `nand)     (x ∷ y ∷ [])  = not (x ∧ y) ∷ []
(≈ `seq s t)  vs            = let ws = (≈ s) vs in (≈ t) ws
(≈ `mix c)    vs            = Vec.map (Vec.lookup vs) c
(≈ `par s t)  vs            =
  let (vsₗ ,, vsᵣ ,, _) = splitAt _ vs in
  (≈ s) vsₗ ++ (≈ t) vsᵣ

tabulate : Vec Bool o → Term stg dyn `⟨ 0 ∣ o ⟩ ε
tabulate {o = zero}  vs        = `mix []
tabulate {o = suc o} (v ∷ vs)  = `par (`const v) (tabulate vs)

replicateₙ : (o : ℕ) → Term stg dyn `⟨ 1 ∣ o ⟩ ε
replicateₙ o = `mix (Vec.replicate o zero)

duplicateₙ : (i : ℕ) → Term stg dyn `⟨ i ∣ i + i ⟩ ε
duplicateₙ i = let all = Vec.allFin i in `mix (all ++ all)

double : ℕ → ℕ
double zero = zero
double (suc n) = 2 + double n

interleaveₙ : (i : ℕ) → Term stg dyn `⟨ i + i ∣ double i ⟩ ε
interleaveₙ 0 = `mix []
interleaveₙ 1 = `mix (Vec.allFin 2)
interleaveₙ (suc i) = let [1⋯i] = Vec.tail $ Vec.allFin (suc i) in
  `seq (`mix ( (zero ↑ˡ suc i)
             ∷ (suc i ↑ʳ zero)
             ∷ Vec.map (_↑ˡ suc i) [1⋯i]
            ++ Vec.map (suc i ↑ʳ_) [1⋯i]))
       (`par `id₂ (interleaveₙ i))

zipWithₙ : (i : ℕ) → Term stg dyn `⟨ 2 ∣ 1 ⟩ ε →
           Term stg dyn `⟨ double i ∣ i ⟩ ε
zipWithₙ 0       op = `mix []
zipWithₙ 1       op = op
zipWithₙ (suc i) op = `par op (zipWithₙ i op)

pointwiseₙ :
    (op : Term stg dyn `⟨ 2 ∣ 1 ⟩ ε) →
    (s t : Term stg dyn `⟨ i ∣ o ⟩ ε) →
    Term stg dyn `⟨ i ∣ o ⟩ ε
pointwiseₙ {i} {o} op s t
  = `seq (duplicateₙ i)
  $ `seq (`par s t)
  $ `seq (interleaveₙ o)
  $ zipWithₙ o op

⟪_⟫ : (Vec Bool i → Vec Bool o) → Term stg dyn `⟨ i ∣ o ⟩ ε
⟪_⟫ {i = 0} f = tabulate (f [])
⟪_⟫ {i = suc i} {o = o} f
  = let [1⋯i] = Vec.tail $ Vec.allFin (suc i) in
    pointwiseₙ `or
      (pointwiseₙ `and (`seq (`mix [1⋯i]) ⟪ f ∘ (true ∷_) ⟫)
        (`seq (`mix (zero ∷ []))            (replicateₙ o)))
      (pointwiseₙ `and (`seq (`mix [1⋯i]) ⟪ f ∘ (false ∷_) ⟫)
        (`seq (`mix (zero ∷ [])) (`seq `not (replicateₙ o))))

cast : (st : _) → Term stg dyn `⟨ i ∣ o ⟩ ε → Value st `⟨ i ∣ o ⟩
cast sta v = v
cast dyn v = v

-- Evaluation function turning source terms into values provided
-- we have an environment assigning values to variables
\end{code}
%<*evaldecl>
\begin{code}
eval : Env Γ → Term src st A Γ → Value st A
\end{code}
%</evaldecl>
%<*eval>
\begin{code}
eval ρ (`var v)    = ρ .lookup v
eval ρ (`app f t)  = eval ρ f (eval ρ t)
eval ρ (`lam b)    = body ρ b
eval ρ `⟨ t ⟩      = eval ρ t
eval ρ (`∼ v)      = eval ρ v
eval ρ (`run t)    = ≈ eval ρ t
eval ρ (`tab {st = st} f) = cast st ⟪ eval ρ f ⟫
eval ρ (`const b)  = `const b
eval ρ `nand       = `nand
eval ρ (`par s t)  = `par (eval ρ s) (eval ρ t)
eval ρ (`seq s t)  = `seq (eval ρ s) (eval ρ t)
eval ρ (`mix k)    = `mix k
\end{code}
%</eval>
\begin{code}
eval ρ `true = true
eval ρ `false = false
eval ρ `ifte = if_then_else_
eval ρ `nil = []
eval ρ `cons = _∷_
eval ρ `split = λ k vvs → k (Vec.head vvs) (Vec.tail vvs)
\end{code}

%<*body>
\begin{code}
body ρ b = λ v → eval (extend ρ v) b
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
stage = eval (λ where .lookup ())
\end{code}
%</stagefun>
\begin{code}


open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Tests for the staging evaluator

infix 0 _∋_↝_
_∋_↝_ : (A : Type dyn) → Term src dyn A ε → Term stg dyn (asStaged A) ε → Set
A ∋ s ↝ t = stage s ≡ t

testNot :
\end{code}
%<*testNot>
\begin{code}
  `⟨ 1 ∣ 1 ⟩ ∋ `not ↝ `seq `dup `nand
\end{code}
%</testNot>
\begin{code}
testNot = refl



testSwap : `⟨ 2 ∣ 2 ⟩
           ∋ `tab ( `app `split $ `lam {- x -}
                  $ `app `split $ `lam {- y -} $ `lam {- [] -}
                  $ `app (`app `cons (`var (there here)))
                  $ `app (`app `cons (`var (there (there here))))
                  $ `nil)
           ↝ _
testSwap = refl
\end{code}
