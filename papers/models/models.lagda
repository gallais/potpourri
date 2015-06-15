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

infix 5 _⊆_
data _⊆_ : (Γ Δ : Con) → Set where
  base  : ε ⊆ ε
  pop!  : {Γ Δ : Con} {σ : ty} (pr : Γ ⊆ Δ) → Γ ∙ σ ⊆ Δ ∙ σ
  step  : {Γ Δ : Con} {σ : ty} (pr : Γ ⊆ Δ) → Γ ⊆ Δ ∙ σ 

wk^∈ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (pr : σ ∈ Γ) → σ ∈ Δ
wk^∈ base        ()
wk^∈ (pop! inc)  here!       = here!
wk^∈ (pop! inc)  (there pr)  = there $′ wk^∈ inc pr
wk^∈ (step inc)  pr          = there $′ wk^∈ inc pr

wk^⊢ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢ σ) → Δ ⊢ σ
wk^⊢ inc (`var v)       = `var $′ wk^∈ inc v
wk^⊢ inc (t `$ u)       = wk^⊢ inc t `$ wk^⊢ inc u
wk^⊢ inc (`λ t)         = `λ $′ wk^⊢ (pop! inc) t
wk^⊢ inc `⟨⟩            = `⟨⟩
wk^⊢ inc `tt            = `tt
wk^⊢ inc `ff            = `ff
wk^⊢ inc (`ifte b l r)  = `ifte (wk^⊢ inc b) (wk^⊢ inc l) (wk^⊢ inc r)
\end{code}

\subsection{The Preoder of Context Inclusions}

\begin{code}
refl : {Γ : Con} → Γ ⊆ Γ
refl {ε}      = base
refl {Γ ∙ σ}  = pop! refl

trans : {Γ Δ Θ : Con} → Γ ⊆ Δ → Δ ⊆ Θ → Γ ⊆ Θ
trans inc₁         base         = inc₁
trans (pop! inc₁)  (pop! inc₂)  = pop! $ trans inc₁ inc₂
trans (step inc₁)  (pop! inc₂)  = step $ trans inc₁ inc₂
trans inc₁         (step inc₂)  = step $ trans inc₁ inc₂
\end{code}

\section{A Notion of Environments}

Environments are defined as the pointwise lifting of a relation \AB{R}
between contexts and types to a relation between two contexts. We can
naturally define a notion of lookup retrieving the proof corresponding
to a specific de Bruijn index.

\begin{code}
infix 5 _[_]_
_[_]_ : (Δ : Con) (R : (Δ : Con) (σ : ty) → Set) (Γ : Con) → Set
Δ [ R ] ε      = ⊤
Δ [ R ] Γ ∙ σ  = Δ [ R ] Γ × R Δ σ


_‼_ :  {Δ : Con} {R : (Δ : Con) (σ : ty) → Set} {Γ : Con}
       (ρ : Δ [ R ] Γ) {σ : ty} (v : σ ∈ Γ) → R Δ σ
(_ , r) ‼ here!    = r
(ρ , _) ‼ there v  = ρ ‼ v
\end{code}

This definition allows for the mechanical lifting of properties on \AB{R}
to properties on environments defined by \AB{R}. We only introduce the ones
we will need subsequently: entailment, weakening and reflexivity. This
notions having been made formal, we can now start studying various models.

\begin{code}
infixr 5 _<$>_
_<$>_ :  {R S : (Δ : Con) (σ : ty) → Set}
         (f : {Δ : Con} {σ : ty} (r : R Δ σ) → S Δ σ)
         {Γ Δ : Con} → Δ [ R ] Γ → Δ [ S ] Γ
_<$>_ f {ε      } ρ       = ρ
_<$>_ f {Γ ∙ σ  } (ρ , r) = f <$> ρ , f r

wk[_] : {Δ : Con} {R : (Δ : Con) (σ : ty) → Set}
        (wk : {Θ : Con} (inc : Δ ⊆ Θ) {σ : ty} → R Δ σ → R Θ σ)
        {Γ : Con} {Θ : Con} (inc : Δ ⊆ Θ) (ρ : Δ [ R ] Γ) →  Θ [ R ] Γ
wk[ wk ] {ε}     inc ρ       = ρ
wk[ wk ] {Γ ∙ σ} inc (ρ , r) = wk[ wk ] inc ρ , wk inc r

infix 5 refl[_,_]_
refl[_,_]_ :  {R : (Δ : Con) (σ : ty) → Set}
              (var : {Δ : Con} {σ : ty} (pr : σ ∈ Δ) → R Δ σ)
              (wk : {Δ Θ : Con} (inc : Δ ⊆ Θ) {σ : ty} → R Δ σ → R Θ σ)
              (Γ : Con) → Γ [ R ] Γ
refl[ var , wk ] ε        = tt
refl[ var , wk ] (Γ ∙ σ)  = wk[ wk ] (step refl) (refl[ var , wk ] Γ) , var here!
\end{code}

\begin{code}
pure : {Δ : Con} {R : (Δ : Con) (σ : ty) → Set}
       {Γ : Con} (f : (σ : ty) (pr : σ ∈ Γ) → R Δ σ) → Δ [ R ] Γ
pure {Γ = ε}     f = tt
pure {Γ = Γ ∙ σ} f = pure (λ σ → f σ ∘ there) , f σ here!

infix 5 _⊆′_
_⊆′_ : (Γ Δ : Con) → Set
_⊆′_ = flip _[ flip _∈_ ]_

wk′^∈ : {Δ Γ : Con} (inc : Γ ⊆′ Δ) {σ : ty} (pr : σ ∈ Γ) → σ ∈ Δ
wk′^∈ inc pr = inc ‼ pr

wk′[_] : {Δ : Con} {R : (Δ : Con) (σ : ty) → Set}
        (wk : {Θ : Con} (inc : Δ ⊆′ Θ) {σ : ty} → R Δ σ → R Θ σ)
        {Γ : Con} {Θ : Con} (inc : Δ ⊆′ Θ) (ρ : Δ [ R ] Γ) →  Θ [ R ] Γ
wk′[ wk ] {ε}     inc ρ       = ρ
wk′[ wk ] {Γ ∙ σ} inc (ρ , r) = wk′[ wk ] inc ρ , wk inc r

refl′ : {Γ : Con} → Γ ⊆′ Γ
refl′ = pure (λ _ → id)

trans′ : {Γ Δ Θ : Con} → Γ ⊆′ Δ → Δ ⊆′ Θ → Γ ⊆′ Θ
trans′ inc₁ inc₂ = wk′[ wk′^∈ ] inc₂ inc₁

step′ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆′ Δ) → Γ ⊆′ Δ ∙ σ
step′ inc = trans′ inc $ pure (λ _ → there)

pop′ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆′ Δ) → Γ ∙ σ ⊆′ Δ ∙ σ
pop′ inc = wk′[ wk′^∈  ] (pure (λ _ → there)) inc , here!

wk′^⊢ : {Δ Γ : Con} (inc : Γ ⊆′ Δ) {σ : ty} (ne : Γ ⊢ σ) → Δ ⊢ σ
wk′^⊢ inc (`var v)       = `var $′ wk′^∈ inc v
wk′^⊢ inc (t `$ u)       = wk′^⊢ inc t `$ wk′^⊢ inc u
wk′^⊢ inc (`λ t)         = `λ $′ wk′^⊢ (pop′ inc) t
wk′^⊢ inc `⟨⟩            = `⟨⟩
wk′^⊢ inc `tt            = `tt
wk′^⊢ inc `ff            = `ff
wk′^⊢ inc (`ifte b l r)  = `ifte (wk′^⊢ inc b) (wk′^⊢ inc l) (wk′^⊢ inc r)
\end{code}

\section{Parallel Substitution}

Parallel substitution can already be seen as a model
construction\todo{mention weakening}:
given a term \AB{t} of type \AB{Γ} \AD{⊢} \AB{σ} and a substitution
\AB{ρ} assigning to each variable of type \AB{σ} in \AB{t} a whole
term of type \AB{Δ} \AD{⊢} \AB{σ}, one can construct a new term of
type \AB{Δ} \AD{⊢} \AB{σ} by keeping \AB{t}'s structure and replacing
its variables by the corresponding terms.

\begin{code}
var‿0 : {Γ : Con} {σ : ty} → Γ ∙ σ ⊢ σ
var‿0 = `var here!

infix 10 ⟦_⟧_
⟦_⟧_ : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊢_ ] Γ) → Δ ⊢ σ
⟦ `var v       ⟧ ρ = ρ ‼ v
⟦ t `$ u       ⟧ ρ = ⟦ t ⟧ ρ `$ ⟦ u ⟧ ρ
⟦ `λ t         ⟧ ρ = `λ $′ ⟦ t ⟧ (wk[ wk^⊢ ] (step refl) ρ , var‿0)
⟦ `⟨⟩          ⟧ ρ = `⟨⟩
⟦ `tt          ⟧ ρ = `tt
⟦ `ff          ⟧ ρ = `ff
⟦ `ifte b l r  ⟧ ρ = `ifte (⟦ b ⟧ ρ) (⟦ l ⟧ ρ) (⟦ r ⟧ ρ)

_⟨_/var₀⟩ : {Γ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
t ⟨ u /var₀⟩ = ⟦ t ⟧ (refl[ `var , wk^⊢ ] _ , u)

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

wk^βξη : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (T : Γ ⊨^βξη σ) → Δ ⊨^βξη σ
wk^βξη inc {`Unit   } T = T
wk^βξη inc {`Bool   } T = wk^nf inc T
wk^βξη inc {σ `→ τ  } T = λ inc′ → T $′ trans inc inc′
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
infix 10 ⟦_⟧^βξη_
⟦_⟧^βξη_ : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊨^βξη_ ] Γ) → Δ ⊨^βξη σ
⟦ `var v       ⟧^βξη ρ = ρ ‼ v
⟦ t `$ u       ⟧^βξη ρ = ⟦ t ⟧^βξη ρ $^βξη ⟦ u ⟧^βξη ρ
⟦ `λ t         ⟧^βξη ρ = λ inc u → ⟦ t ⟧^βξη (wk[ wk^βξη ] inc ρ , u)
⟦ `⟨⟩          ⟧^βξη ρ = tt
⟦ `tt          ⟧^βξη ρ = `tt
⟦ `ff          ⟧^βξη ρ = `ff
⟦ `ifte b l r  ⟧^βξη ρ = ifte^βξη (⟦ b ⟧^βξη ρ) (⟦ l ⟧^βξη ρ) (⟦ r ⟧^βξη ρ)

diag^βξη : (Γ : Con) → Γ [ _⊨^βξη_ ] Γ
diag^βξη Γ = refl[ reflect^βξη _ ∘ `var , wk^βξη ] Γ

eval^βξη : (Γ : Con) {σ : ty} (t : Γ ⊢ σ) → Γ ⊨^βξη σ
eval^βξη Γ t = ⟦ t ⟧^βξη diag^βξη Γ

norm^βξη : (Γ : Con) (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^nf σ
norm^βξη Γ σ t = reify^βξη σ $′ eval^βξη Γ t
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

wk^βξ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (T : Γ ⊨^βξ σ) → Δ ⊨^βξ σ
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

infix 10 ⟦_⟧^βξ_
⟦_⟧^βξ_ : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊨^βξ_ ] Γ) → Δ ⊨^βξ σ
⟦ `var v       ⟧^βξ ρ = ρ ‼ v
⟦ t `$ u       ⟧^βξ ρ = ⟦ t ⟧^βξ ρ $^βξ ⟦ u ⟧^βξ ρ
⟦ `λ t         ⟧^βξ ρ = inj₂ $ λ {_} inc u → ⟦ t ⟧^βξ (wk[ wk^βξ ] inc ρ , u)
⟦ `⟨⟩          ⟧^βξ ρ = inj₂ $ tt
⟦ `tt          ⟧^βξ ρ = inj₂ $ true
⟦ `ff          ⟧^βξ ρ = inj₂ $ false
⟦ `ifte b l r  ⟧^βξ ρ = ifte^βξ (⟦ b ⟧^βξ ρ) (⟦ l ⟧^βξ ρ) (⟦ r ⟧^βξ ρ)

diag^βξ : (Γ : Con) → Γ [ _⊨^βξ_ ] Γ
diag^βξ Γ = refl[ reflect^βξ _ ∘ `var , wk^βξ ] Γ

eval^βξ : (Γ : Con) {σ : ty} (t : Γ ⊢ σ) → Γ ⊨^βξ σ
eval^βξ Γ t = ⟦ t ⟧^βξ diag^βξ Γ

norm^βξ : (Γ : Con) (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^nf σ
norm^βξ Γ σ t = reify^βξ σ $′ eval^βξ Γ t
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

wk^β : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (T : Γ ⊨^β σ) → Δ ⊨^β σ
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

infix 10 ⟦_⟧^β_
⟦_⟧^β_ : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊨^β_ ] Γ) → Δ ⊨^β σ
⟦ `var v       ⟧^β ρ = ρ ‼ v
⟦ t `$ u       ⟧^β ρ = ⟦ t ⟧^β ρ $^β ⟦ u ⟧^β ρ
⟦ `λ t         ⟧^β ρ = ⟦ `λ t ⟧ (source <$> ρ) , inj₂ (λ inc u → ⟦ t ⟧^β (wk[ wk^β ] inc ρ , u))
⟦ `⟨⟩          ⟧^β ρ = `⟨⟩ , inj₂ tt
⟦ `tt          ⟧^β ρ = `tt , inj₂ true
⟦ `ff          ⟧^β ρ = `ff , inj₂ false
⟦ `ifte b l r  ⟧^β ρ = ifte^β (⟦ b ⟧^β ρ) (⟦ l ⟧^β ρ) (⟦ r ⟧^β ρ)

diag^β : (Γ : Con) → Γ [ _⊨^β_ ] Γ
diag^β Γ = refl[ reflect^β _ ∘ `var , wk^β ] Γ

eval^β : (Γ : Con) {σ : ty} (t : Γ ⊢ σ) → Γ ⊨^β σ
eval^β Γ t = ⟦ t ⟧^β diag^β Γ

norm^β : (Γ : Con) (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^whnf σ
norm^β Γ σ t = reify^β σ $′ eval^β Γ t
\end{code}

\bibliographystyle{apalike}
\bibliography{main}

\end{document}
