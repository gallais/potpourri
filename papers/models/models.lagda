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

\include{commands}

\title{Glueing Terms to Models: \\ Variations on Normalization by Evaluation}
\author{}

\begin{document}

\maketitle{}
Normalization by Evaluation is a technique leveraging the computational
power of a host language in order to normalize expressions of a deeply
embedded one. The process is based on a model construction associating
to each context \AB{Γ} and type \AB{σ}, a set of values \model{}. Two
procedures are then defined: the first one produces elements of \model{}
provided a well-typed term of the corresponding \AB{Γ} \AD{⊢} \AB{σ} type
and an interpretation for the variables in \AB{Γ} whilst the second one
extracts, in a type-directed manner, normal forms \AB{Γ} \AD{⊢^{nf}} \AB{σ}
from elements of the model \model{}. Normalization is achieved by composing
the two procedures.

The traditional model construction produces β-normal η-long terms
whereas evaluation strategies implemented in proof systems tend to
avoid applying η-rules as much as possible: quite unsurprisingly,
when typechecking large developments expanding the proof terms is
a really bad idea. In these systems, normal forms are neither η-long
nor η-short: the η-rule is actually never considered except when
comparing two terms for equality, one of which is neutral whilst
the other is constructor-headed.

This decision to lazily apply the η-rule can be pushed further: one may
forgo using the ξ-rule and simply perform weak-head normalization, pushing
the computation further only when absolutely necessary e.g. when the
two terms compared for equality have matching head constructors.

This paper shows how these different evaluation strategies emerge naturally
as variations on Normalization by Evaluation obtained by enriching the
traditional model with extra syntactical artefacts in a manner reminiscent
of Coquand and Dybjer's approach to defining a Normalization by Evaluation
procedure for the SK combinator calculus~\cite{CoqDybSK}. Their resorting
to glueing terms to elements of the model was dictated by the sheer impossibily
to write a sensible reification procedure but, in hindsight, it provides
us with a powerful technique to build models deciding alternative equational
theories.

\paragraph{Outline} We start by defining the simple calculus we will use
as a running example, we then recall the usual model construction and show
how to exploit it to implement a normalization function for the equational
theory given by the βξη rules. The main contribution of the article consists
of us building alternative models retaining more and more syntactical
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

\begin{code}
data ty : Set where
  `Unit  : ty
  `Bool  : ty
  _`→_   : (σ τ : ty) → ty

data Con : Set where
  ε    : Con
  _∙_  : (Γ : Con) (σ : ty) → Con

infix 5 _[_]_
_[_]_ : (Δ : Con) (R : (Δ : Con) (σ : ty) → Set) (Γ : Con) → Set
Δ [ R ] ε      = ⊤
Δ [ R ] Γ ∙ σ  = Δ [ R ] Γ × R Δ σ

_<$>_ :  {R S : (Δ : Con) (σ : ty) → Set}
         (f : {Δ : Con} {σ : ty} (r : R Δ σ) → S Δ σ)
         {Γ Δ : Con} → Δ [ R ] Γ → Δ [ S ] Γ
_<$>_ f {ε      } ρ       = ρ
_<$>_ f {Γ ∙ σ  } (ρ , r) = f <$> ρ , f r

infix 1 _∈_
data _∈_ (σ : ty) : (Γ : Con) → Set where
  here!  : {Γ : Con} → σ ∈ Γ ∙ σ
  there  : {Γ : Con} {τ : ty} (pr : σ ∈ Γ) → σ ∈ Γ ∙ τ

_‼_ :  {Δ : Con} {R : (Δ : Con) (σ : ty) → Set} {Γ : Con}
       (ρ : Δ [ R ] Γ) {σ : ty} (v : σ ∈ Γ) → R Δ σ
(_ , r)  ‼ here!    = r
(ρ , _)  ‼ there v  = ρ ‼ v

infix 1 _⊆_

data _⊆_ : (Γ Δ : Con) → Set where
  base  : ε ⊆ ε
  pop!  : {Γ Δ : Con} {σ : ty} (pr : Γ ⊆ Δ) → Γ ∙ σ ⊆ Δ ∙ σ
  step  : {Γ Δ : Con} {σ : ty} (pr : Γ ⊆ Δ) → Γ ⊆ Δ ∙ σ 

refl : {Γ : Con} → Γ ⊆ Γ
refl {ε}      = base
refl {Γ ∙ σ}  = pop! refl

trans : {Γ Δ Θ : Con} → Γ ⊆ Δ → Δ ⊆ Θ → Γ ⊆ Θ
trans inc₁         base         = inc₁
trans (pop! inc₁)  (pop! inc₂)  = pop! $ trans inc₁ inc₂
trans (step inc₁)  (pop! inc₂)  = step $ trans inc₁ inc₂
trans inc₁         (step inc₂)  = step $ trans inc₁ inc₂

wk[_] : {Δ : Con} {R : (Δ : Con) (σ : ty) → Set}
        (wk : {Θ : Con} (inc : Δ ⊆ Θ) {σ : ty} → R Δ σ → R Θ σ)
        {Γ : Con} {Θ : Con} (inc : Δ ⊆ Θ) (ρ : Δ [ R ] Γ) →  Θ [ R ] Γ
wk[ wk ] {ε}     inc ρ       = ρ
wk[ wk ] {Γ ∙ σ} inc (ρ , r) = wk[ wk ] inc ρ , wk inc r


refl[_,_]_ :  {R : (Δ : Con) (σ : ty) → Set}
              (var : {Δ : Con} {σ : ty} (pr : σ ∈ Δ) → R Δ σ)
              (wk : {Δ Θ : Con} (inc : Δ ⊆ Θ) {σ : ty} → R Δ σ → R Θ σ)
              (Γ : Con) → Γ [ R ] Γ
refl[ var , wk ] ε        = tt
refl[ var , wk ] (Γ ∙ σ)  = wk[ wk ] (step refl) (refl[ var , wk ] Γ) , var here!

wk∈ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (pr : σ ∈ Γ) → σ ∈ Δ
wk∈ base        ()
wk∈ (pop! inc)  here!       = here!
wk∈ (pop! inc)  (there pr)  = there $′ wk∈ inc pr
wk∈ (step inc)  pr          = there $′ wk∈ inc pr

infix 5 _⊢_
data _⊢_ (Γ : Con) : (σ : ty) → Set where
  `var   : {σ : ty} (v : σ ∈ Γ) → Γ ⊢ σ
  _`$_   : {σ τ : ty} (t : Γ ⊢ σ `→ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
  `λ     : {σ τ : ty} (t : Γ ∙ σ ⊢ τ) → Γ ⊢ σ `→ τ
  `⟨⟩    : Γ ⊢ `Unit
  `tt    : Γ ⊢ `Bool
  `ff    : Γ ⊢ `Bool
  `ifte  : {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ) → Γ ⊢ σ

wk⊢ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢ σ) → Δ ⊢ σ
wk⊢ inc (`var v)       = `var $′ wk∈ inc v
wk⊢ inc (t `$ u)       = wk⊢ inc t `$ wk⊢ inc u
wk⊢ inc (`λ t)         = `λ $′ wk⊢ (pop! inc) t
wk⊢ inc `⟨⟩            = `⟨⟩
wk⊢ inc `tt            = `tt
wk⊢ inc `ff            = `ff
wk⊢ inc (`ifte b l r)  = `ifte (wk⊢ inc b) (wk⊢ inc l) (wk⊢ inc r)

var‿0 : {Γ : Con} {σ : ty} → Γ ∙ σ ⊢ σ
var‿0 = `var here!

⟦_⟧_ : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊢_ ] Γ) → Δ ⊢ σ
⟦ `var v       ⟧ ρ = ρ ‼ v
⟦ t `$ u       ⟧ ρ = ⟦ t ⟧ ρ `$ ⟦ u ⟧ ρ
⟦ `λ t         ⟧ ρ = `λ $′ ⟦ t ⟧ (wk[ wk⊢ ] (step refl) ρ , var‿0)
⟦ `⟨⟩          ⟧ ρ = `⟨⟩
⟦ `tt          ⟧ ρ = `tt
⟦ `ff          ⟧ ρ = `ff
⟦ `ifte b l r  ⟧ ρ = `ifte (⟦ b ⟧ ρ) (⟦ l ⟧ ρ) (⟦ r ⟧ ρ)

_⟨_/var₀⟩ : {Γ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
t ⟨ u /var₀⟩ = ⟦ t ⟧ (refl[ `var , wk⊢ ] _ , u)

eta : {Γ : Con} {σ τ : ty} (t : Γ ⊢ σ `→ τ) → Γ ⊢ σ `→ τ
eta t = `λ (wk⊢ (step refl) t `$ var‿0)
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
  wk^ne inc (`var v)        = `var $′ wk∈ inc v
  wk^ne inc (ne `$ u)       = wk^ne inc ne `$ wk^nf inc u
  wk^ne inc (`ifte ne l r)  = `ifte (wk^ne inc ne) (wk^nf inc l) (wk^nf inc r)

  wk^nf : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^nf σ) → Δ ⊢^nf σ
  wk^nf inc (`embed t)  = `embed $′ wk^ne inc t
  wk^nf inc `⟨⟩         = `⟨⟩
  wk^nf inc `tt         = `tt
  wk^nf inc `ff         = `ff
  wk^nf inc (`λ nf)     = `λ $′ wk^nf (pop! inc) nf

wk^whne : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^whne σ) → Δ ⊢^whne σ
wk^whne inc (`var v)        = `var $′ wk∈ inc v
wk^whne inc (ne `$ u)       = wk^whne inc ne `$ wk⊢ inc u
wk^whne inc (`ifte ne l r)  = `ifte (wk^whne inc ne) (wk⊢ inc l) (wk⊢ inc r)

wk^whnf : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^whnf σ) → Δ ⊢^whnf σ
wk^whnf inc (`embed t)  = `embed $′ wk^whne inc t
wk^whnf inc `⟨⟩         = `⟨⟩
wk^whnf inc `tt         = `tt
wk^whnf inc `ff         = `ff
wk^whnf inc (`λ b)      = `λ $′ wk⊢ (pop! inc) b

\end{code}

\section{Normalization by Evaluation for βξη}

\begin{code}
infix 5 _⊨^βξη_
_⊨^βξη_ : (Γ : Con) (σ : ty) → Set
Γ ⊨^βξη `Unit   = ⊤
Γ ⊨^βξη `Bool   = Γ ⊢^ne `Bool ⊎ Bool
Γ ⊨^βξη σ `→ τ  = {Δ : Con} (inc : Γ ⊆ Δ) (u : Δ ⊨^βξη σ) → Δ ⊨^βξη τ

wk^βξη : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (T : Γ ⊨^βξη σ) → Δ ⊨^βξη σ
wk^βξη inc {`Unit   } T = T
wk^βξη inc {`Bool   } T = [ inj₁ ∘ wk^ne inc , inj₂ ]′ T
wk^βξη inc {σ `→ τ  } T = λ inc′ → T $′ trans inc inc′

_$^βξη_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βξη σ `→ τ) (u : Γ ⊨^βξη σ) → Γ ⊨^βξη τ
t $^βξη u = t refl u

mutual

  var‿0^βξη : {Γ : Con} {σ : ty} → Γ ∙ σ ⊨^βξη σ
  var‿0^βξη = reflect^βξη _ $′ `var here!

  reflect^βξη : {Γ : Con} (σ : ty) (t : Γ ⊢^ne σ) → Γ ⊨^βξη σ
  reflect^βξη `Unit     t = tt
  reflect^βξη `Bool     t = inj₁ t
  reflect^βξη (σ `→ τ)  t = λ inc u → reflect^βξη τ $′ wk^ne inc t `$ reify^βξη σ u

  reify^βξη : {Γ : Con} (σ : ty) (T : Γ ⊨^βξη σ) → Γ ⊢^nf σ
  reify^βξη `Unit     T          = `⟨⟩
  reify^βξη `Bool     (inj₁ ne)  = `embed ne
  reify^βξη `Bool     (inj₂ T)   = if T then `tt else `ff
  reify^βξη (σ `→ τ)  T          = `λ $′ reify^βξη τ $′ T (step refl) var‿0^βξη

ifte^βξη : {Γ : Con} {σ : ty} (b : Γ ⊨^βξη `Bool) (l r : Γ ⊨^βξη σ) → Γ ⊨^βξη σ
ifte^βξη (inj₁ T) l r = reflect^βξη _ $′ `ifte T (reify^βξη _ l) (reify^βξη _ r)
ifte^βξη (inj₂ T) l r = if T then l else r

⟦_⟧^βξη_ : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊨^βξη_ ] Γ) → Δ ⊨^βξη σ
⟦ `var v       ⟧^βξη ρ = ρ ‼ v
⟦ t `$ u       ⟧^βξη ρ = ⟦ t ⟧^βξη ρ $^βξη ⟦ u ⟧^βξη ρ
⟦ `λ t         ⟧^βξη ρ = λ inc u → ⟦ t ⟧^βξη (wk[ wk^βξη ] inc ρ , u)
⟦ `⟨⟩          ⟧^βξη ρ = tt
⟦ `tt          ⟧^βξη ρ = inj₂ true
⟦ `ff          ⟧^βξη ρ = inj₂ false
⟦ `ifte b l r  ⟧^βξη ρ = ifte^βξη (⟦ b ⟧^βξη ρ) (⟦ l ⟧^βξη ρ) (⟦ r ⟧^βξη ρ)

diag^βξη : (Γ : Con) → Γ [ _⊨^βξη_ ] Γ
diag^βξη Γ = refl[ reflect^βξη _ ∘ `var , wk^βξη ] Γ

norm^βξη : (Γ : Con) (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^nf σ
norm^βξη Γ σ t = reify^βξη σ $′ ⟦ t ⟧^βξη (diag^βξη Γ)
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

_$^βξ_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βξ σ `→ τ) (u : Γ ⊨^βξ σ) → Γ ⊨^βξ τ
inj₁ ne  $^βξ u = inj₁ $ ne `$ reify^βξ _ u
inj₂ F   $^βξ u = F refl u

ifte^βξ : {Γ : Con} {σ : ty} (b : Γ ⊨^βξ `Bool) (l r : Γ ⊨^βξ σ) → Γ ⊨^βξ σ
ifte^βξ (inj₁ ne) l r = inj₁ $ `ifte ne (reify^βξ _ l) (reify^βξ _ r)
ifte^βξ (inj₂ T)  l r = if T then l else r

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

norm^βξ : (Γ : Con) (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^nf σ
norm^βξ Γ σ t = reify^βξ σ $′ ⟦ t ⟧^βξ (diag^βξ Γ)
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
wk^β inc (t , inj₁ ne)  = wk⊢ inc t , inj₁ (wk^whne inc ne)
wk^β inc (t , inj₂ T)   = wk⊢ inc t , inj₂ (wk^β⋆ inc T)

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

_$^β_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^β σ `→ τ) (u : Γ ⊨^β σ) → Γ ⊨^β τ
(t , inj₁ ne)  $^β (u , U) = t `$ u , inj₁ (ne `$ u)
(t , inj₂ T)   $^β (u , U) = t `$ u , proj₂ (T refl (u , U))

ifte^β : {Γ : Con} {σ : ty} (b : Γ ⊨^β `Bool) (l r : Γ ⊨^β σ) → Γ ⊨^β σ
ifte^β (b , inj₁ ne)  (l , L) (r , R) = `ifte b l r , inj₁ (`ifte ne l r)
ifte^β (b , inj₂ B)   (l , L) (r , R) = `ifte b l r , (if B then L else R)

⟦_⟧^β_ : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊨^β_ ] Γ) → Δ ⊨^β σ
⟦ `var v       ⟧^β ρ = ρ ‼ v
⟦ t `$ u       ⟧^β ρ = ⟦ t ⟧^β ρ $^β ⟦ u ⟧^β ρ
⟦ `λ t         ⟧^β ρ = ⟦ `λ t ⟧ (source <$> ρ) , inj₂ (λ inc u → ⟦ t ⟧^β (wk[ wk^β ] inc ρ , u))
⟦ `⟨⟩          ⟧^β ρ = `⟨⟩ , inj₂ tt
⟦ `tt          ⟧^β ρ = `tt , inj₂ true
⟦ `ff          ⟧^β ρ = `ff , inj₂ false
⟦ `ifte b l r  ⟧^β ρ = ifte^β (⟦ b ⟧^β ρ) (⟦ l ⟧^β ρ) (⟦ r ⟧^β ρ)

diag^β : (Γ : Con) → Γ [ _⊨^βξ_ ] Γ
diag^β Γ = refl[ reflect^βξ _ ∘ `var , wk^βξ ] Γ

norm^β : (Γ : Con) (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^nf σ
norm^β Γ σ t = reify^βξ σ $′ ⟦ t ⟧^βξ (diag^βξ Γ)
\end{code}

\bibliographystyle{apalike}
\bibliography{main}

\end{document}
