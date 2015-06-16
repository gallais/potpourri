\documentclass{article}
\usepackage{fullpage}
\usepackage{amsthm, amsmath}
\usepackage{mathpartir}
\usepackage[english]{babel}
\usepackage[references]{agda}
\usepackage{hyperref}
\usepackage{xargs}

\usepackage{todonotes}
\usepackage{float}
\floatstyle{boxed}
\restylefloat{figure}

\setmainfont[Ligatures=TeX]{XITS}
\setmathfont{XITS Math}

%\renewcommand{\baselinestretch}{1.5} 
\include{commands}

\title{Glueing Terms to Models: \\ Variations on Normalization by Evaluation}
\author{}

\begin{document}

\maketitle{}
Normalization by Evaluation is a technique leveraging the computational
power of a host language in order to normalize expressions of a deeply
embedded one. The process is based on a model construction associating
to each context \AB{Γ} and type \AB{σ}, a type of values \model{}. Two
procedures are then defined: the first one (\AF{eval}) produces elements
of \model{} provided a well-typed term of the corresponding \AB{Γ} \AD{⊢}
\AB{σ} type and an interpretation for the variables in \AB{Γ} whilst
the second one (\AF{reify}) extracts, in a type-directed manner, normal
forms \AB{Γ} \AD{⊢^{nf}} \AB{σ} from elements of the model \model{}.
Normalization is achieved by composing the two procedures.

The traditional typed model construction leads to a normalization procedure
producing β-normal η-long terms. However evaluation strategies implemented
in actual proof systems tend to avoid applying η-rules as much as possible:
quite unsurprisingly, when typechecking complex developments expanding the
proof terms is a really bad idea. In these systems, normal forms are neither
η-long nor η-short: the η-rule is actually never considered except when
comparing two terms for equality, one of which is neutral whilst the other
is constructor-headed. Instead of declaring them to be distinct, the algorithm
will perform one step of η-expansion on the neutral term and keep comparing
their subterms structurally. The conversion test will only fail when confronted
with two neutral terms which have distinct head variables or two normal forms
with distinct head constructors.

This decision to lazily apply the η-rule can be pushed further: one may
forgo using the ξ-rule and simply perform weak-head normalization, pursuing
the computation only when absolutely necessary e.g. when the two terms
compared for equality have matching head constructors and these constructors'
arguments need therefore to be inspected.

This paper shows how these different evaluation strategies emerge naturally
as variations on Normalization by Evaluation. They may be obtained by
enriching the traditional model with extra syntactical artefacts in a manner
reminiscent of Coquand and Dybjer's approach to defining a Normalization by
Evaluation procedure for the SK combinator calculus~\cite{CoqDybSK}. Their
resorting to glueing terms to elements of the model was dictated by the
sheer impossibily to write a sensible reification procedure but, in hindsight,
it provides us with a powerful technique to build models internalizing
alternative equational theories.

\paragraph{Outline} We shall start by defining the simple calculus we will use
as a running example, then recall the usual model construction and show
how to exploit it to implement a normalization function for the equational
theory given by the βξη rules. The main contribution of the article consists
of us building alternative models retaining more and more syntactic
information about the source term which gave rise to the model's element
thus allowing us to decide weaker equational theories corresponding to the
βξ rules first and to β alone finally.


\paragraph{Notations} In all of our constructions, we carefully highlight the
fact that similar definitions are introduced by using the same names suffixed
with a superscript listing the set of rules handled by this construction. These
similarities mainly reflect the fact that any model of the lambda calculus will
be applicative in nature. For more details, see e.g. \cite{mitchell1996foundations}.

\AgdaHide{
\begin{code}
module models where

open import Level
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Function

infixr 1 _$′_
_$′_ : {A B : Set} (f : A → B) (a : A) → B
_$′_ = _$_
\end{code}}

\section{The calculus}

We are going to illustrate these constructions using a simply-typed calculus
with Bool and Unit as base type. In order to be able to build terms which are
well-scoped and well-typed by construction, we need a notion of contexts
(represented as snoc lists of types) and positions in them (represented as
strongly-typed de Bruijn indices~\cite{de1972lambda}). Finally, we can define
a notion of context inclusion and prove that it induces a notion of weakening
on de Bruijn indices as well as proof terms.

\begin{code}
infix 10 _`→_
data ty : Set where
  `Unit  : ty
  `Bool  : ty
  _`→_   : (σ τ : ty) → ty

infixl 10 _∙_
data Con : Set where
  ε    : Con
  _∙_  : (Γ : Con) (σ : ty) → Con

infix 5 _∈_
data _∈_ (σ : ty) : (Γ : Con) → Set where
  here!  : {Γ : Con} → σ ∈ Γ ∙ σ
  there  : {Γ : Con} {τ : ty} (pr : σ ∈ Γ) → σ ∈ Γ ∙ τ

infix 5 _⊢_
infixl 5 _`$_ 
data _⊢_ (Γ : Con) : (σ : ty) → Set where
  `var   : {σ : ty} (v : σ ∈ Γ) → Γ ⊢ σ
  _`$_   : {σ τ : ty} (t : Γ ⊢ σ `→ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
  `λ     : {σ τ : ty} (t : Γ ∙ σ ⊢ τ) → Γ ⊢ σ `→ τ
  `⟨⟩    : Γ ⊢ `Unit
  `tt    : Γ ⊢ `Bool
  `ff    : Γ ⊢ `Bool
  `ifte  : {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ) → Γ ⊢ σ
\end{code}

\section{A Notion of Environments}

Environments are defined as the pointwise lifting of a relation \AB{R}
between contexts and types to a relation between two contexts. We can
naturally define a notion of lookup retrieving the proof corresponding
to a specific de Bruijn index.

\begin{code}
infix 5 _[_]_
_[_]_ : {ℓ : Level} (Δ : Con) (R : (Δ : Con) (σ : ty) → Set ℓ) (Γ : Con) → Set ℓ
Δ [ R ] ε      = Lift ⊤
Δ [ R ] Γ ∙ σ  = Δ [ R ] Γ × R Δ σ

pure : {ℓ : Level} {Δ : Con} {R : (Δ : Con) (σ : ty) → Set ℓ}
       {Γ : Con} (f : (σ : ty) (pr : σ ∈ Γ) → R Δ σ) → Δ [ R ] Γ
pure {Γ = ε}     f = lift tt
pure {Γ = Γ ∙ σ} f = pure (λ σ → f σ ∘ there) , f σ here!

infix 5 _‼_
_‼_ :  {ℓ : Level} {Δ : Con} {R : (Δ : Con) (σ : ty) → Set ℓ} {Γ : Con} {σ : ty}
       (ρ : Δ [ R ] Γ) (v : σ ∈ Γ) → R Δ σ
(_ , r) ‼ here!    = r
(ρ , _) ‼ there v  = ρ ‼ v
\end{code}

\subsection{The Preoder of Context Inclusions}

\begin{code}
infix 5 _⊆_

_⊆_ : (Γ Δ : Con) → Set
_⊆_ = flip _[ flip _∈_ ]_

wk[_] : {ℓ : Level} {Δ : Con} {R : (Δ : Con) (σ : ty) → Set ℓ}
        (wk : {Θ : Con} {σ : ty} (inc : Δ ⊆ Θ) → R Δ σ → R Θ σ)
        {Γ Θ : Con} (inc : Δ ⊆ Θ) (ρ : Δ [ R ] Γ) →  Θ [ R ] Γ
wk[ wk ] {ε}     inc ρ       = ρ
wk[ wk ] {Γ ∙ σ} inc (ρ , r) = wk[ wk ] inc ρ , wk inc r

wk^∈ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) (pr : σ ∈ Γ) → σ ∈ Δ
wk^∈ = _‼_

refl : {Γ : Con} → Γ ⊆ Γ
refl = pure (λ _ → id)

trans : {Γ Δ Θ : Con} → Γ ⊆ Δ → Δ ⊆ Θ → Γ ⊆ Θ
trans inc₁ inc₂ = wk[ wk^∈ ] inc₂ inc₁

pop! : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) → Γ ∙ σ ⊆ Δ ∙ σ
pop! inc = wk[ wk^∈  ] (pure (λ _ → there)) inc , here!

step : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) → Γ ⊆ Δ ∙ σ
step inc = trans inc $ pure (λ _ → there)
\end{code}

\section{Semantics and Generic Evaluation Function}

In order to have the opportunity to focus on the model constructions
rather than defining over and over again similar-looking evaluation
functions, we introduce the notions of \AR{Semantics} and generically
define an evaluation function parametrised over such semantics.
We will see later on that this notion is generic enough to encompass
a large body of traversals from simple renamings to the more complex
evaluation into a model.

A \AR{Semantics} packs two main concepts and the methods based on them
necessary to construct an evaluation function. First, Environment values
(\ARF{𝓔}) are defined; we require that there is a way to apply weakening
to such elements (\ARF{wk}) as well as a way to create new ones from
variables (\ARF{embed}). Then, the model (\ARF{𝓜}) is introduced together
with the semantic counterparts of the language's constructors. Most of
them have the type one would expect except for two interesting cases. The
semantic counterpart of the variable constructor (\ARF{⟦var⟧}) is a
function converting environment values into model ones. And the semantic
λ-abstraction (\ARF{⟦λ⟧}) is an actual function which, in any extended
context, takes an \emph{environment} value and delivers one in the model.

\begin{code}
record Semantics (ℓᴱ ℓᴹ : Level) : Set (suc (ℓᴱ ⊔ ℓᴹ)) where
  infixl 5 _⟦$⟧_
  field
    -- environment values and corresponding methods
    𝓔       : (Δ : Con) (σ : ty) → Set ℓᴱ
    wk      : {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) (r : 𝓔 Γ σ) → 𝓔 Δ σ
    embed   : {Γ : Con} {σ : ty} (pr : σ ∈ Γ) → 𝓔 Γ σ
    -- model and semantic counterparts of the constructors
    𝓜       : (Δ : Con) (σ : ty) → Set ℓᴹ
    ⟦var⟧   : {Γ : Con} {σ : ty} → 𝓔 Γ σ → 𝓜 Γ σ
    _⟦$⟧_   : {Γ : Con} {σ τ : ty} → 𝓜 Γ (σ `→ τ) → 𝓜 Γ σ → 𝓜 Γ τ
    ⟦λ⟧     : {Γ : Con} {σ τ : ty} (t : {Δ : Con} (pr : Γ ⊆ Δ) (u : 𝓔 Δ σ) → 𝓜 Δ τ) → 𝓜 Γ (σ `→ τ)
    ⟦⟨⟩⟧    : {Γ : Con} → 𝓜 Γ `Unit
    ⟦tt⟧    : {Γ : Con} → 𝓜 Γ `Bool
    ⟦ff⟧    : {Γ : Con} → 𝓜 Γ `Bool
    ⟦ifte⟧  : {Γ : Con} {σ : ty} (b : 𝓜 Γ `Bool) (l r : 𝓜 Γ σ) → 𝓜 Γ σ
\end{code}

The evaluation function is defined by replacing each constructor with
their semantic counterpart in order to combine the induction hypothesis
given by the subterms. In the λ-abstraction case, the environment is
weakened so that the returned value indeed resides in the extended context.
Finally, one can build a diagonal environment by \ARF{embed}ding its
variables.

\begin{code}
infix 10 _⊨⟦_⟧_ _⊨eval_
_⊨⟦_⟧_ : {ℓᴱ ℓᴹ : Level} (Sem : Semantics ℓᴱ ℓᴹ) (open Semantics Sem) →
         {Δ Γ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ 𝓔 ] Γ) → 𝓜 Δ σ
Sem ⊨⟦ `var v       ⟧ ρ = let open Semantics Sem in ⟦var⟧ $ ρ ‼ v
Sem ⊨⟦ t `$ u       ⟧ ρ = let open Semantics Sem in Sem ⊨⟦ t ⟧ ρ ⟦$⟧ Sem ⊨⟦ u ⟧ ρ
Sem ⊨⟦ `λ t         ⟧ ρ = let open Semantics Sem in ⟦λ⟧ λ inc u → Sem ⊨⟦ t ⟧ (wk[ wk ] inc ρ , u)
Sem ⊨⟦ `⟨⟩          ⟧ ρ = let open Semantics Sem in ⟦⟨⟩⟧
Sem ⊨⟦ `tt          ⟧ ρ = let open Semantics Sem in ⟦tt⟧
Sem ⊨⟦ `ff          ⟧ ρ = let open Semantics Sem in ⟦ff⟧
Sem ⊨⟦ `ifte b l r  ⟧ ρ = let open Semantics Sem in ⟦ifte⟧ (Sem ⊨⟦ b ⟧ ρ) (Sem ⊨⟦ l ⟧ ρ) (Sem ⊨⟦ r ⟧ ρ)

_⊨eval_ : {ℓᴱ ℓᴹ : Level} (Sem : Semantics ℓᴱ ℓᴹ) (open Semantics Sem) →
          {Γ : Con} {σ : ty} (t : Γ ⊢ σ) → 𝓜 Γ σ
Sem ⊨eval t = let open Semantics Sem in Sem ⊨⟦ t ⟧ pure (λ _ → embed)
\end{code}

\section{Renaming}

Our first example of a semantics is the syntactic model: using variables
as environment values and terms as elements of the model and constructors
as their own semantic counterpart, we obtain a rather involved definition
of the identity function as \AF{Renaming} \AF{⊨eval\_}. But this construction
is not at all useless: indeed, the more general \AF{Renaming} \AF{⊨⟦\_⟧\_}
turns out to be precisely the notion of weakening for terms we will need
later on.

\begin{code}
Renaming : Semantics zero zero
Renaming =
  record  { 𝓔       = flip _∈_
          ; 𝓜      = _⊢_
          ; embed   = id
          ; wk      = wk^∈
          ; ⟦var⟧   = `var
          ; _⟦$⟧_   = _`$_
          ; ⟦λ⟧     = λ t → `λ (t (step refl) here!)
          ; ⟦⟨⟩⟧    = `⟨⟩
          ; ⟦tt⟧    = `tt
          ; ⟦ff⟧    = `ff
          ; ⟦ifte⟧  = `ifte
          }

wk^⊢ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) (t : Γ ⊢ σ) → Δ ⊢ σ
wk^⊢ = flip $ Renaming ⊨⟦_⟧_
\end{code}

\section{Parallel Substitution}

Our second example of a semantics is another spin on the syntactic
model: the environment values are now terms (but the diagonal
environment will be only made up of variables) and so are the model's
values. Once more the semantic function \AF{Substitution} \AF{⊨⟦\_⟧\_}
is more interesting than the evaluation one: it is an implementation
of parallel substitution.

\begin{code}
var‿0 : {Γ : Con} {σ : ty} → Γ ∙ σ ⊢ σ
var‿0 = `var here!

Substitution : Semantics zero zero
Substitution =
  record  { 𝓔       = _⊢_
          ; 𝓜       = _⊢_
          ; embed   = `var
          ; wk      = wk^⊢ 
          ; ⟦var⟧   = id
          ; _⟦$⟧_   = _`$_
          ; ⟦λ⟧     = λ t → `λ (t (step refl) var‿0)
          ; ⟦⟨⟩⟧    = `⟨⟩
          ; ⟦tt⟧    = `tt
          ; ⟦ff⟧    = `ff
          ; ⟦ifte⟧  = `ifte
          }

infix 10 ⟦_⟧_
⟦_⟧_ : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊢_ ] Γ) → Δ ⊢ σ
⟦_⟧_ = Substitution ⊨⟦_⟧_

_⟨_/var₀⟩ : {Γ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
t ⟨ u /var₀⟩ = ⟦ t ⟧ (pure (λ _ → `var) , u)

eta : {Γ : Con} {σ τ : ty} (t : Γ ⊢ σ `→ τ) → Γ ⊢ σ `→ τ
eta t = `λ (wk^⊢ (step refl) t `$ var‿0)
\end{code}

\subsection{Recalling the three reduction rules}

\begin{mathpar}
\inferrule{
  }{\text{(\AIC{`λ} \AB{t}) \AIC{`\$} \AB{u} ↝ \AB{t} \AF{⟨} \AB{u} \AF{/var₀⟩}}
  }{β}
\and
\inferrule{\text{\AB{t} ↝ \AB{t′}}
  }{\text{\AIC{`λ} \AB{t} ↝ \AIC{`λ} \AB{t′}}
  }{ξ}
\and
\inferrule{
  }{\text{\AB{t} ↝ \AF{eta} \AB{t}}
  }{η}
\end{mathpar}

\section{(Weak) Normal Forms}

\begin{code}
mutual
  infix 5 _⊢^ne_ _⊢^nf_
  data _⊢^ne_ (Γ : Con) (σ : ty) : Set where
    `var   : (v : σ ∈ Γ) → Γ ⊢^ne σ
    _`$_   : {τ : ty} (t : Γ ⊢^ne τ `→ σ) (u : Γ ⊢^nf τ) → Γ ⊢^ne σ
    `ifte  : (b : Γ ⊢^ne `Bool) (l r : Γ ⊢^nf σ) → Γ ⊢^ne σ

  -- todo: promotion generic nf!
  data _⊢^nf_ (Γ : Con) : (σ : ty) → Set where
    `embed  : {σ : ty} (t : Γ ⊢^ne σ) → Γ ⊢^nf σ
    `⟨⟩     : Γ ⊢^nf `Unit
    `tt     : Γ ⊢^nf `Bool
    `ff     : Γ ⊢^nf `Bool
    `λ      : {σ τ : ty} (b : Γ ∙ σ ⊢^nf τ) → Γ ⊢^nf σ `→ τ

mutual
  infix 5 _⊢^whne_ _⊢^whnf_
  data _⊢^whne_ (Γ : Con) (σ : ty) : Set where
    `var   : (v : σ ∈ Γ) → Γ ⊢^whne σ
    _`$_   : {τ : ty} (t : Γ ⊢^whne τ `→ σ) (u : Γ ⊢ τ) → Γ ⊢^whne σ
    `ifte  : (b : Γ ⊢^whne `Bool) (l r : Γ ⊢ σ) → Γ ⊢^whne σ

  data _⊢^whnf_ (Γ : Con) : (σ : ty) → Set where
    `embed  : {σ : ty} (t : Γ ⊢^whne σ) → Γ ⊢^whnf σ
    `⟨⟩     : Γ ⊢^whnf `Unit
    `tt     : Γ ⊢^whnf `Bool
    `ff     : Γ ⊢^whnf `Bool
    `λ      : {σ τ : ty} (b : Γ ∙ σ ⊢ τ) → Γ ⊢^whnf σ `→ τ

mutual

  wk^ne : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^ne σ) → Δ ⊢^ne σ
  wk^ne inc (`var v)        = `var $′ wk^∈ inc v
  wk^ne inc (ne `$ u)       = wk^ne inc ne `$ wk^nf inc u
  wk^ne inc (`ifte ne l r)  = `ifte (wk^ne inc ne) (wk^nf inc l) (wk^nf inc r)

  wk^nf : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^nf σ) → Δ ⊢^nf σ
  wk^nf inc (`embed t)  = `embed $′ wk^ne inc t
  wk^nf inc `⟨⟩         = `⟨⟩
  wk^nf inc `tt         = `tt
  wk^nf inc `ff         = `ff
  wk^nf inc (`λ nf)     = `λ $′ wk^nf (pop! inc) nf

wk^whne : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^whne σ) → Δ ⊢^whne σ
wk^whne inc (`var v)        = `var $′ wk^∈ inc v
wk^whne inc (ne `$ u)       = wk^whne inc ne `$ wk^⊢ inc u
wk^whne inc (`ifte ne l r)  = `ifte (wk^whne inc ne) (wk^⊢ inc l) (wk^⊢ inc r)

wk^whnf : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^whnf σ) → Δ ⊢^whnf σ
wk^whnf inc (`embed t)  = `embed $′ wk^whne inc t
wk^whnf inc `⟨⟩         = `⟨⟩
wk^whnf inc `tt         = `tt
wk^whnf inc `ff         = `ff
wk^whnf inc (`λ b)      = `λ $′ wk^⊢ (pop! inc) b

\end{code}

\section{Normalization by Evaluation for βξη}

In this section we recall the usual model construction and the corresponding
normalization function. The definition of the model enforces that η-expansion
is applied eagerly: all inhabitants of \AB{Γ} \AF{⊨^βξη} \AIC{`Unit} are indeed
equal and all elements of \AB{Γ} \AF{⊨^βξη} \AB{σ} \AIC{`→} \AB{τ} are functions
in Agda meaning that their reifications will only ever be \AIC{`λ}-headed.

\begin{code}
infix 5 _⊨^βξη_
_⊨^βξη_ : (Γ : Con) (σ : ty) → Set
Γ ⊨^βξη `Unit   = ⊤
Γ ⊨^βξη `Bool   = Γ ⊢^nf `Bool
Γ ⊨^βξη σ `→ τ  = {Δ : Con} (inc : Γ ⊆ Δ) (u : Δ ⊨^βξη σ) → Δ ⊨^βξη τ

wk^βξη : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) (T : Γ ⊨^βξη σ) → Δ ⊨^βξη σ
wk^βξη {σ = `Unit   } inc T = T
wk^βξη {σ = `Bool   } inc T = wk^nf inc T
wk^βξη {σ = σ `→ τ  } inc T = λ inc′ → T $′ trans inc inc′
\end{code}

In order to have a clean definition of the evaluation function \AF{⟦\_⟧^βξη\_},
we factor out the semantic notion of application and conditional branching.
Application is straightforward thanks to the fact that semantic functions are
Agda functions. Conditional Branching on the other hand is a bit more subtle:
because the boolean value may be a neutral term, we are forced to define the
reflection and reification mechanisms first to be able to reflect the stuck
term into the model. The practical implication of this is that stuck \AIC{`ifte}
will be effectively η-expanded.

\begin{code}
infixr 5 _$^βξη_
_$^βξη_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βξη σ `→ τ) (u : Γ ⊨^βξη σ) → Γ ⊨^βξη τ
t $^βξη u = t refl u

mutual

  var‿0^βξη : {Γ : Con} {σ : ty} → Γ ∙ σ ⊨^βξη σ
  var‿0^βξη = reflect^βξη _ $′ `var here!

  reflect^βξη : {Γ : Con} (σ : ty) (t : Γ ⊢^ne σ) → Γ ⊨^βξη σ
  reflect^βξη `Unit     t = tt
  reflect^βξη `Bool     t = `embed t
  reflect^βξη (σ `→ τ)  t = λ inc u → reflect^βξη τ $′ wk^ne inc t `$ reify^βξη σ u

  reify^βξη : {Γ : Con} (σ : ty) (T : Γ ⊨^βξη σ) → Γ ⊢^nf σ
  reify^βξη `Unit     T = `⟨⟩
  reify^βξη `Bool     T = T
  reify^βξη (σ `→ τ)  T = `λ $′ reify^βξη τ $′ T (step refl) var‿0^βξη

ifte^βξη : {Γ : Con} {σ : ty} (b : Γ ⊨^βξη `Bool) (l r : Γ ⊨^βξη σ) → Γ ⊨^βξη σ
ifte^βξη (`embed T)  l r = reflect^βξη _ $′ `ifte T (reify^βξη _ l) (reify^βξη _ r)
ifte^βξη `tt         l r = l
ifte^βξη `ff         l r = r
\end{code}

The evaluation function is then defined mostly by using the semantic
counterparts of each constructor to combine the results obtained
recursively. The \AIC{`λ} case is slightly more involved given that
one needs to be able to handle any extension of the context which is
possible by weakening the environment along the provided inclusion
proof. Normalization is obtained by combining evaluation with reification,
using the fact that we can build an initial environment by η-expanding all
variables in scope.

\begin{code}
Normalize^βξη : Semantics zero zero
Normalize^βξη =
  record  { 𝓔       = _⊨^βξη_
          ; 𝓜       = _⊨^βξη_
          ; embed   = reflect^βξη _ ∘ `var
          ; wk      = wk^βξη
          ; ⟦var⟧   = id
          ; _⟦$⟧_   = _$^βξη_
          ; ⟦λ⟧     = id
          ; ⟦⟨⟩⟧    = tt
          ; ⟦tt⟧    = `tt
          ; ⟦ff⟧    = `ff
          ; ⟦ifte⟧  = ifte^βξη
          }

infix 10 ⟦_⟧^βξη_
⟦_⟧^βξη_ : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊨^βξη_ ] Γ) → Δ ⊨^βξη σ
⟦_⟧^βξη_ = Normalize^βξη ⊨⟦_⟧_

norm^βξη : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^nf σ
norm^βξη σ t = reify^βξη σ $′ Normalize^βξη ⊨eval t
\end{code}

\section{Normalization by Evaluation for βξ}

\begin{code}
mutual

  infix 5 _⊨^βξ_ _⊨^βξ⋆_
  _⊨^βξ_ : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βξ σ  = Γ ⊢^ne σ
            ⊎ Γ ⊨^βξ⋆ σ

  _⊨^βξ⋆_ : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βξ⋆ `Unit   = ⊤
  Γ ⊨^βξ⋆ `Bool   = Bool
  Γ ⊨^βξ⋆ σ `→ τ  = {Δ : Con} (inc : Γ ⊆ Δ) (u : Δ ⊨^βξ σ) → Δ ⊨^βξ τ

wk^βξ⋆ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (T : Γ ⊨^βξ⋆ σ) → Δ ⊨^βξ⋆ σ
wk^βξ⋆ inc {`Unit   } T = T
wk^βξ⋆ inc {`Bool   } T = T
wk^βξ⋆ inc {σ `→ τ  } T = λ inc′ → T $′ trans inc inc′

wk^βξ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) (T : Γ ⊨^βξ σ) → Δ ⊨^βξ σ
wk^βξ inc (inj₁ ne) = inj₁ $ wk^ne inc ne
wk^βξ inc (inj₂ T)  = inj₂ $ wk^βξ⋆ inc T

var‿0^βξ : {Γ : Con} {σ : ty} → Γ ∙ σ ⊨^βξ σ
var‿0^βξ = inj₁ (`var here!)

reflect^βξ : {Γ : Con} (σ : ty) (t : Γ ⊢^ne σ) → Γ ⊨^βξ σ
reflect^βξ σ t = inj₁ t

mutual

  reify^βξ⋆ : {Γ : Con} (σ : ty) (T : Γ ⊨^βξ⋆ σ) → Γ ⊢^nf σ
  reify^βξ⋆ `Unit     T = `⟨⟩
  reify^βξ⋆ `Bool     T = if T then `tt else `ff
  reify^βξ⋆ (σ `→ τ)  T = `λ $′ reify^βξ τ $′ T (step refl) var‿0^βξ

  reify^βξ : {Γ : Con} (σ : ty) (T : Γ ⊨^βξ σ) → Γ ⊢^nf σ
  reify^βξ σ (inj₁ ne)  = `embed ne
  reify^βξ σ (inj₂ T)   = reify^βξ⋆ σ T

infixr 5 _$^βξ_
_$^βξ_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βξ σ `→ τ) (u : Γ ⊨^βξ σ) → Γ ⊨^βξ τ
inj₁ ne  $^βξ u = inj₁ $ ne `$ reify^βξ _ u
inj₂ F   $^βξ u = F refl u

ifte^βξ : {Γ : Con} {σ : ty} (b : Γ ⊨^βξ `Bool) (l r : Γ ⊨^βξ σ) → Γ ⊨^βξ σ
ifte^βξ (inj₁ ne) l r = inj₁ $ `ifte ne (reify^βξ _ l) (reify^βξ _ r)
ifte^βξ (inj₂ T)  l r = if T then l else r


Normalize^βξ : Semantics zero zero
Normalize^βξ =
  record  { 𝓔       = _⊨^βξ_
          ; 𝓜       = _⊨^βξ_
          ; embed   = reflect^βξ _ ∘ `var
          ; wk      = wk^βξ
          ; ⟦var⟧   = id
          ; _⟦$⟧_   = _$^βξ_
          ; ⟦λ⟧     = inj₂
          ; ⟦⟨⟩⟧    = inj₂ tt
          ; ⟦tt⟧    = inj₂ true
          ; ⟦ff⟧    = inj₂ false
          ; ⟦ifte⟧  = ifte^βξ
          }

infix 10 ⟦_⟧^βξ_
⟦_⟧^βξ_ : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊨^βξ_ ] Γ) → Δ ⊨^βξ σ
⟦_⟧^βξ_ = Normalize^βξ ⊨⟦_⟧_

norm^βξ : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^nf σ
norm^βξ σ t = reify^βξ σ $′ Normalize^βξ ⊨eval t
\end{code}

\section{Normalization by Evaluation for β}


\begin{code}

erase^whne : {Γ : Con} {σ : ty} (t : Γ ⊢^whne σ) → Γ ⊢ σ
erase^whne (`var v)       = `var v
erase^whne (t `$ u)       = erase^whne t `$ u
erase^whne (`ifte t l r)  = `ifte (erase^whne t) l r

erase^whnf : {Γ : Con} {σ : ty} (t : Γ ⊢^whnf σ) → Γ ⊢ σ
erase^whnf (`embed t)  = erase^whne t
erase^whnf `⟨⟩         = `⟨⟩
erase^whnf `tt         = `tt
erase^whnf `ff         = `ff
erase^whnf (`λ b)      = `λ b


mutual

  infix 5 _⊨^β_ _⊨^β⋆_
  _⊨^β_ : (Γ : Con) (σ : ty) → Set
  Γ ⊨^β σ  = Γ ⊢ σ ×  ( Γ ⊢^whne σ
                      ⊎ Γ ⊨^β⋆ σ)

  _⊨^β⋆_ : (Γ : Con) (σ : ty) → Set
  Γ ⊨^β⋆ `Unit   = ⊤
  Γ ⊨^β⋆ `Bool   = Bool
  Γ ⊨^β⋆ σ `→ τ  = {Δ : Con} (inc : Γ ⊆ Δ) (u : Δ ⊨^β σ) → Δ ⊨^β τ

wk^β⋆ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (T : Γ ⊨^β⋆ σ) → Δ ⊨^β⋆ σ
wk^β⋆ inc {`Unit   } T = T
wk^β⋆ inc {`Bool   } T = T
wk^β⋆ inc {σ `→ τ  } T = λ inc′ → T $′ trans inc inc′

wk^β : {Δ Γ : Con}{σ : ty} (inc : Γ ⊆ Δ) (T : Γ ⊨^β σ) → Δ ⊨^β σ
wk^β inc (t , inj₁ ne)  = wk^⊢ inc t , inj₁ (wk^whne inc ne)
wk^β inc (t , inj₂ T)   = wk^⊢ inc t , inj₂ (wk^β⋆ inc T)

reflect^β : {Γ : Con} (σ : ty) (t : Γ ⊢^whne σ) → Γ ⊨^β σ
reflect^β σ t = erase^whne t , inj₁ t

var‿0^β : {Γ : Con} {σ : ty} → Γ ∙ σ ⊨^β σ
var‿0^β = `var here! , inj₁ (`var here!)

source : {Γ : Con} {σ : ty} (T : Γ ⊨^β σ) → Γ ⊢ σ
source (t , _) = t

mutual

  reify^β⋆ : {Γ : Con} (σ : ty) (T : Γ ⊨^β⋆ σ) → Γ ⊢^whnf σ
  reify^β⋆ `Unit     T = `⟨⟩
  reify^β⋆ `Bool     T = if T then `tt else `ff
  reify^β⋆ (σ `→ τ)  T = `λ $′ proj₁ (T (step refl) var‿0^β)

  reify^β : {Γ : Con} (σ : ty) (T : Γ ⊨^β σ) → Γ ⊢^whnf σ
  reify^β σ (t , inj₁ ne) = `embed ne
  reify^β σ (t , inj₂ T)  = reify^β⋆ σ T

infixr 5 _$^β_
_$^β_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^β σ `→ τ) (u : Γ ⊨^β σ) → Γ ⊨^β τ
(t , inj₁ ne)  $^β (u , U) = t `$ u , inj₁ (ne `$ u)
(t , inj₂ T)   $^β (u , U) = t `$ u , proj₂ (T refl (u , U))

ifte^β : {Γ : Con} {σ : ty} (b : Γ ⊨^β `Bool) (l r : Γ ⊨^β σ) → Γ ⊨^β σ
ifte^β (b , inj₁ ne)  (l , L) (r , R) = `ifte b l r , inj₁ (`ifte ne l r)
ifte^β (b , inj₂ B)   (l , L) (r , R) = `ifte b l r , (if B then L else R)


Normalize^β : Semantics zero zero
Normalize^β =
  record  { 𝓔       = _⊨^β_
          ; 𝓜       = _⊨^β_
          ; embed   = reflect^β _ ∘ `var
          ; wk      = wk^β
          ; ⟦var⟧   = id
          ; _⟦$⟧_   = _$^β_
          ; ⟦λ⟧     = λ t → `λ (source (t (step refl) var‿0^β)) , inj₂ t
          ; ⟦⟨⟩⟧    = `⟨⟩ , inj₂ tt
          ; ⟦tt⟧    = `tt , inj₂ true
          ; ⟦ff⟧    = `ff , inj₂ false
          ; ⟦ifte⟧  = ifte^β
          }

infix 10 ⟦_⟧^β_
⟦_⟧^β_ : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊨^β_ ] Γ) → Δ ⊨^β σ
⟦_⟧^β_ = Normalize^β ⊨⟦_⟧_

norm^β : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^whnf σ
norm^β σ t = reify^β σ $′ Normalize^β ⊨eval t
\end{code}

\bibliographystyle{apalike}
\bibliography{main}

\end{document}
