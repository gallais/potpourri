\begin{code}
module STLC where

open import Function.Base using (_∘_)
open import Data.Product using (_×_)
open import Agda.Builtin.Equality using (_≡_; refl)

infixr 5 _`⇒_
\end{code}
%<*type>
\begin{code}
data Type : Set where
  `α    : Type
  _`⇒_  : (A B : Type) → Type
\end{code}
%</type>
\begin{code}

\end{code}
%<*typevariables>
\begin{code}
variable A B C : Type
\end{code}
%</typevariables>
\begin{code}

\end{code}
%<*context>
\begin{code}
data Context : Set where
  ε    : Context
  _,_  : Context → Type → Context

variable Γ Δ Θ : Context
variable P Q : Context → Set
\end{code}
%</context>
\begin{code}


variable I J : Set

\end{code}
%<*forall>
\begin{code}
∀[_] : (I → Set) → Set
∀[ P ] = ∀ {i} → P i
\end{code}
%</forall>
\begin{code}

infixl 5 _⊢_
\end{code}
%<*update>
\begin{code}
_⊢_ : (I → J) → (J → Set) → (I → Set)
(f ⊢ P) i = P (f i)
\end{code}
%</update>
\begin{code}

infixr 3 _⇒_
\end{code}
%<*arrow>
\begin{code}
_⇒_ : (P Q : I → Set) → (I → Set)
(P ⇒ Q) i = P i → Q i
\end{code}
%</arrow>
\begin{code}

infixr 4 _∩_
\end{code}
%<*product>
\begin{code}
_∩_ : (P Q : I → Set) → (I → Set)
(P ∩ Q) i = P i × Q i
\end{code}
%</product>
\begin{code}

module PRINTONLY where

  swapType : (P Q : Context → Set) (A : Type) → Set
  swapType P Q A =
\end{code}
%<*swaptype>
\begin{code}
    ∀[ (_, A) ⊢ (P ∩ Q ⇒ Q ∩ P) ]
\end{code}
%</swaptype>
\begin{code}

  _ : (P Q : Context → Set) (A : Type) → swapType P Q A ≡ (
\end{code}
%<*swaptypenormalised>
\begin{code}
    ∀ {Γ} → (P (Γ , A) × Q (Γ , A)) → (Q (Γ , A) × P (Γ , A))
\end{code}
%</swaptypenormalised>
\begin{code}
    )
  _ = λ P Q A → refl

\end{code}
%<*varnormalised>
\begin{code}
  data Var : Type → Context → Set where
    here   : ∀ {Γ} →            Var A (Γ , A)
    there  : ∀ {Γ} → Var A Γ →  Var A (Γ , B)
\end{code}
%</varnormalised>
\begin{code}

\end{code}
%<*var>
\begin{code}
data Var : Type → Context → Set where
  here   : ∀[          (_, A) ⊢ Var A ]
  there  : ∀[ Var A ⇒  (_, B) ⊢ Var A ]
\end{code}
%</var>
\begin{code}

module PRINTONLY2 where

  \end{code}
  %<*termdecl>
  \begin{code}
  data Term : Type → Context → Set where
  \end{code}
  %</termdecl>
  %<*termvar>
  \begin{code}
    `var  : ∀[  Var A ⇒
             ----------
                Term A ]
  \end{code}
  %</termvar>
  %<*termapp>
  \begin{code}
    `app  : ∀[  Term (A `⇒ B) ⇒ Term A ⇒
             ------------------------
                Term B ]
  \end{code}
  %</termapp>
  %<*termlam>
  \begin{code}
    `lam  : ∀[  (_, A) ⊢ Term B ⇒
             ----------------
                Term (A `⇒ B) ]
  \end{code}
  %</termlam>
  \begin{code}


\end{code}
%<*term>
\begin{code}
data Term : Type → Context → Set where
  `var  : ∀[ Var A ⇒ Term A ]
  `app  : ∀[ Term (A `⇒ B) ⇒ Term A ⇒ Term B ]
  `lam  : ∀[ (_, A) ⊢ Term B ⇒ Term (A `⇒ B) ]
\end{code}
%</term>
\begin{code}

\end{code}
%<*id>
\begin{code}
`id : ∀[ Term (A `⇒ A) ]
`id = `lam (`var here)
\end{code}
%</id>
\begin{code}
infix 0 _≤_
\end{code}
%<*ope>
\begin{code}
data _≤_ : Context → Context → Set where
  done  : ε ≤ ε
  keep  : Γ ≤ Δ → Γ , A  ≤ Δ , A
  drop  : Γ ≤ Δ → Γ      ≤ Δ , A
\end{code}
%</ope>
\begin{code}

\end{code}
%<*lerefl>
\begin{code}
≤-refl : Γ ≤ Γ
\end{code}
%</lerefl>
\begin{code}
≤-refl {ε} = done
≤-refl {Γ , x} = keep ≤-refl
\end{code}

%<*weaken>
\begin{code}
Weaken : (Context → Set) → Set
Weaken P = ∀ {Γ Δ} → Γ ≤ Δ → P Γ → P Δ
\end{code}
%</weaken>
\begin{code}

\end{code}
%<*weakVar>
\begin{code}
weak-Var : Weaken (Var A)
weak-Var (drop σ)  v          = there (weak-Var σ v)
weak-Var (keep σ)  here       = here
weak-Var (keep σ)  (there v)  = there (weak-Var σ v)
\end{code}
%</weakVar>
\begin{code}

\end{code}
%<*weakTerm>
\begin{code}
weak-Term : Weaken (Term A)
weak-Term σ (`var v)    = `var (weak-Var σ v)
weak-Term σ (`app f t)  = `app (weak-Term σ f) (weak-Term σ t)
weak-Term σ (`lam b)    = `lam (weak-Term (keep σ) b)
\end{code}
%</weakTerm>
\begin{code}

infixr 3 _`∘_
\end{code}
%<*composition>
\begin{code}
_`∘_    : ∀[ Term (B `⇒ C) ⇒ Term (A `⇒ B) ⇒ Term (A `⇒ C) ]
g `∘ f  =  let Γ≤Γ,A = drop ≤-refl in
           `lam (`app (weak-Term Γ≤Γ,A g) (`app (weak-Term Γ≤Γ,A f) (`var here)))
\end{code}
%</composition>
\begin{code}

\end{code}
%<*box>
\begin{code}
record □ (A : Context → Set) (Γ : Context) : Set where
  constructor mkBox
  field runBox : ∀[ (Γ ≤_) ⇒ A ]
\end{code}
%</box>
\begin{code}
open □

\end{code}
%<*kripke>
\begin{code}
Kripke : (A B : Context → Set) → (Context → Set)
Kripke A B = □ (A ⇒ B)
\end{code}
%</kripke>
\begin{code}

\end{code}
%<*letrans>
\begin{code}
≤-trans : Γ ≤ Δ → Δ ≤ Θ → Γ ≤ Θ
\end{code}
%</letrans>
\begin{code}
≤-trans p (drop q) = drop (≤-trans p q)
≤-trans done done = done
≤-trans (keep p) (keep q) = keep (≤-trans p q)
≤-trans (drop p) (keep q) = drop (≤-trans p q)

\end{code}
%<*extract>
\begin{code}
extract : ∀ {P} → ∀[ □ P ⇒ P ]
extract p = p .runBox ≤-refl
\end{code}
%</extract>
\begin{code}

\end{code}
%<*duplicate>
\begin{code}
duplicate : ∀ {P} → ∀[ □ P ⇒ □ (□ P) ]
duplicate p .runBox σ .runBox = p .runBox ∘ ≤-trans σ
\end{code}
%</duplicate>
\begin{code}

\end{code}
%<*weakKripke>
\begin{code}
weak-Kripke : Weaken (Kripke P Q)
weak-Kripke σ f = duplicate f .runBox σ
\end{code}
%</weakKripke>
\begin{code}

-- application
\end{code}
%<*semapp>
\begin{code}
_$$_ : ∀[ Kripke P Q ⇒ P ⇒ Q ]
_$$_ = extract
\end{code}
%</semapp>
\begin{code}

-- lambda-abstraction
infixr 3 mkBox
\end{code}
%<*mkbox>
\begin{code}
syntax mkBox (λ σ x → b) = λλ[ σ , x ] b
\end{code}
%</mkbox>
\begin{code}

-- Model construction
-- Here we would traditionally enforce that (Value `α)
-- returns neutral terms
\end{code}
%<*value>
\begin{code}
Value : Type → Context → Set
Value `α        = Term `α
Value (A `⇒ B)  = Kripke (Value A) (Value B)
\end{code}
%</value>
\begin{code}

\end{code}
%<*weakValue>
\begin{code}
weak-Value : (A : Type) → Weaken (Value A)
weak-Value `α        σ v = weak-Term σ v
weak-Value (A `⇒ B)  σ v = weak-Kripke σ v
\end{code}
%</weakValue>
\begin{code}

interleaved mutual

  reify    : (A : Type) → ∀[ Value A  ⇒ Term A   ]
  reflect  : (A : Type) → ∀[ Term A   ⇒ Value A  ]

  reify    `α T = T
  reflect  `α t = t

  reify    (A `⇒ B) T = `lam
    let  f  = weak-Kripke (drop ≤-refl) T
         v  = reflect A (`var here)
    in reify B (f $$ v)
  reflect  (A `⇒ B) t = λλ[ σ , V ]
    let  f  = weak-Term σ t
         v  = reify A V
    in reflect B (`app f v)


-- Type of environments mapping variables to values
\end{code}
%<*env>
\begin{code}
record Env (Γ Δ : Context) : Set where
  field lookup : ∀ {A} → Var A Γ → Value A Δ
\end{code}
%</env>
\begin{code}
open Env

\end{code}
%<*extend>
\begin{code}
extend : ∀[ Env Γ ⇒ □ (Value A ⇒ Env (Γ , A)) ]
extend ρ .runBox σ v .lookup here       = v
extend ρ .runBox σ v .lookup (there x)  = weak-Value _ σ (ρ .lookup x)
\end{code}
%</extend>
\begin{code}

\end{code}
%<*eval>
%<*evaldecl>
\begin{code}
eval : Env Γ Δ → Term A Γ → Value A Δ
\end{code}
%</evaldecl>
\begin{code}
eval ρ (`var v)    = ρ .lookup v
eval ρ (`app f t)  = eval ρ f $$ eval ρ t
eval ρ (`lam b)    = λλ[ σ , v ] eval (extend ρ .runBox σ v) b
\end{code}
%</eval>
\begin{code}

init : Env Γ Γ
init .lookup v = reflect _ (`var v)

norm : Term A Γ → Term A Γ
norm = reify _ ∘ eval init

\end{code}
