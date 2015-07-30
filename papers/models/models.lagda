%%%%% Pick one of the three
%\include{articleheader}
%\include{sigplanheader}
\include{lncsheader}
%%%%
\usepackage{mathpartir}
\include{commands}

\begin{document}
\title{Type and Scope Preserving Semantics}
\maketitle{}

\begin{abstract}
We introduce a notion of type and scope preserving semantics
generalising McBride's approach to defining one traversal
generic enough to be instantiated to substitution first and
then renaming. Its careful distinction of environment and
model values as well as its structure typical of a Kripke
semantics make it capable of expressing renaming and substitution
but also various variations on Normalisation by Evaluation as
well as, perhaps more surprisingly, monadic computations such
as a pretty-printing function.

We then demonstrate that expressing these algorithms in a common
framework yields immediate benefits: we can deploy some logical
relations generically over these instances and obtain for instance
the fusion lemmas for renaming, substitution and normalisation by
evaluation as simple corollaries of the appropriate fundamental
lemma.
\end{abstract}

\section*{Introduction}

In order to implement an embedded Domain Specific Language (eDSL), a developer
can opt for either a shallow or a deep embedding. In the shallow approach, she
will use the host language's own types and term constructs to model the domain
specific language's building blocks. This will allow her to rely on any and all
of the host's libraries when writing programs in the eDSL. Should she decide
to use a deep embedding, representing expressions directly as their abstract
syntax tree will allow her to inspect, optimise, and compile terms as she sees
fit. This ability to inspect the tree comes at the cost of having to reimplement
basic notions such as renaming or substitution with the risk of introducing
bugs. Trying to get the compiler to detect these bugs leads to a further
distinction between different kinds of deep embeddings: she may either prove type
and scope safety on paper and use an inductive \emph{type} to describe an \emph{untyped}
syntax, follow Carette, Kiselyov, and Shan~\cite{carette2009finally} and rely on
parametric polymorphism to guarantee the existence of an underlying type and scope
safe term, or use an inductive \emph{family} to represent the term itself whilst
enforcing these invariants in the type.

In previous work, McBride~\cite{mcbride2005type} and Benton, Hur, Kennedy and
McBride~\cite{benton2012strongly} have shown how to alleviate the programmer's
burden when opting for the strongly-typed approach based on inductive families
in Epigram~\cite{mcbride2004view} and Coq~\cite{Coq:manual} respectively. They
both start by defining a traversal generic enough to be instantiated to renaming
first and then substitution. In Benton et al., the bulk of the work has to be
repeated when defining Normalisation by Evaluation. Reasoning about these definitions
is also still mostly done in an ad-hoc manner: Coq's tactics mechanism does help
them to discharge the four fusion lemmas involving renaming and substitution.
But the properties of the evaluation function are established using some more
proof scripts and rely on function extensionality rather than the usual Partial
Equivalence Relation.

We build on their insights and define an abstract notion of \AR{Semantics}
encompassing these two important operations as well as others Carette et al.
could represent (e.g. measuring the size of a term) and even Normalisation
by Evaluation~\cite{berger1991inverse}. By highlighting the common structure
of all of these algorithms, we get the opportunity to not only implement
them but also prove their properties generically.

\paragraph{Outline} We shall start by defining the simple calculus we will use
as a running example. We will then introduce a notion of environments as well
as one well-known instance: the preorder of context inclusions. This will lead
us to defining a generic notion of type and scope-preserving \AR{Semantics} which
can be used to define a generic evaluation function. We will then showcase the
ground covered by these \AR{Semantics}: from the syntactic ones corresponding
to renaming and substitution to pretty-printing or some variations on Normalisation
by Evaluation. Finally, we will demonstrate how, the definition of \AR{Semantics}
being generic enough, we can prove theorems about these evaluation functions.

\paragraph{Notations} This article is a literate Agda file typeset using the
\LaTeX{} backend with as little post-processing as possible: we simply hide
telescopes of implicit arguments and properly display (super / sub)-scripts
as well as special operators such as \AF{>>=} or \AF{++}. As such, a lot of
the notations have a meaning in Agda: \AIC{green} identifiers are data constructors,
\ARF{pink} names refer to record fields, and \AF{blue} is characteristic of
defined symbols. Underscores have a special status: when defining mixfix
identifiers~\cite{danielsson2011parsing}, they mark positions where arguments
may be inserted; our using the development version of Agda means that we have
access to Haskell-style sections i.e. one may write \AF{\_+} \AN{5} for the partial
application of \AF{\_+\_} corresponding to \AS{λ} x \AS{→} \AB{x} \AF{+} \AN{5}
or, to mention something that will appear later on, \AF{Renaming} \AF{⊨⟦\_⟧\_}
for the partial applications of \AF{\_⊨⟦\_⟧\_} to \AF{Renaming}.

\paragraph{Formalisation} This whole development has been checked by Agda~\cite{norell2009dependently}
which guarantees that all constructions are indeed well-typed, and all functions are
total. Nonetheless, it should be noted that the generic model constructions and the
various example of \AR{Semantics} given can be fully replicated in Haskell using GADTs
to describe both the terms themselves and the singletons~\cite{eisenberg2013dependently}
providing the user with the runtime descriptions of their types or their contexts' shapes.
This yields, to the best of our knowledge, the first tagless and typeful implementation
of Normalisation by Evaluation in Haskell. The subtleties of working with dependent types
in Haskell~\cite{lindley2014hasochism} are outside the scope of this paper but we do
provide a (commented) Haskell module containing all the translated definitions.
It should be noted that Danvy, Keller and Puech have achieved a similar goal in
OCaml~\cite{danvytagless} but their formalisation uses Parametric Higher Order Abstract
Syntax which frees them from having to deal with variable binding, contexts and use
models à la Kripke where one may extend the context. However we consider these to be
primordial given that they can still guide the implementation of more complex type
theories where, until now, being typeful is still out of reach but type-level guarantees
about scope preservation still help to root out a lot of bugs.


\AgdaHide{
\begin{code}
{-# OPTIONS --no-eta #-}
module models where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum hiding (map ; [_,_])
open import Data.Product hiding (map)
open import Function

infixr 1 _$′_
_$′_ : {A B : Set} (f : A → B) (a : A) → B
_$′_ = _$_
\end{code}}

\section{The Calculus}

We are going to define and study various semantics for a simply-typed λ-calculus
with \AIC{`Bool} and \AIC{`Unit} as base types as a minimal example of a sum type
and a record type equipped with an η-rule.

\AgdaHide{
\begin{code}
infixr 20 _`→_
\end{code}}
\begin{code}
data ty : Set where
  `Unit  : ty
  `Bool  : ty
  _`→_   : (σ τ : ty) → ty
\end{code}

In order to be able to talk about the type of the variables in scope, we
need a notion of contexts. We choose to represent them as snoc lists of
types; \AIC{ε} denotes the empty context and \AB{Γ} \AIC{∙} \AB{σ} the
context \AB{Γ} extended with a fresh variable of type \AB{σ}. Variables
are then positions in such a context represented as typed de Bruijn
indices~\cite{de1972lambda}.

\AgdaHide{
\begin{code}
infixl 10 _∙_
infix 5 _∈_
\end{code}}
\begin{code}
data Con : Set where
  ε    : Con
  _∙_  : (Γ : Con) (σ : ty) → Con

data _∈_ (σ : ty) : (Γ : Con) → Set where
  here!  : {Γ : Con} → σ ∈ (Γ ∙ σ)
  there  : {Γ : Con} {τ : ty} (pr : σ ∈ Γ) → σ ∈ (Γ ∙ τ)
\end{code}

The syntax for this λ-calculus is designed to guarantee that terms are
well-scoped and well-typed by construction. This presentation due to
Altenkirch and Reus~\cite{altenkirch1999monadic} relies heavily on
Dybjer's inductive families~\cite{dybjer1991inductive}. Rather than
having untyped pre-terms and a typing relation assigning a type to
them, the rules are here enforced in the syntax: we can see for example
that the \AIC{`var} constructor takes a typed de Bruijn index and
constructs a term of the corresponding type; that application (\AIC{\_`\$\_})
takes a function from \AB{σ} to \AB{τ}, an argument of type \AB{σ} living
in the same scope \AB{Γ} and produces a term of type \AB{τ}; or that the
body of a λ-abstraction (\AIC{`λ}) has its context extended with a fresh
variable whose type corresponds to the domain of the function being defined.


\AgdaHide{
\begin{code}
infix 5 _⊢_
infixl 5 _`$_
\end{code}}
\begin{code}
data _⊢_ (Γ : Con) : (σ : ty) → Set where
  `var   : {σ : ty} (v : σ ∈ Γ) → Γ ⊢ σ
  _`$_   : {σ τ : ty} (t : Γ ⊢ (σ `→ τ)) (u : Γ ⊢ σ) → Γ ⊢ τ
  `λ     : {σ τ : ty} (t : Γ ∙ σ ⊢ τ) → Γ ⊢ (σ `→ τ)
  `⟨⟩    : Γ ⊢ `Unit
  `tt    : Γ ⊢ `Bool
  `ff    : Γ ⊢ `Bool
  `ifte  : {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ) → Γ ⊢ σ
\end{code}

\section{A Notion of Environments}

All the semantics we are interested in defining evaluate a term
written in the type-correct representation of the calculus defined
above given an interpretation of its free variables. We call the
collection of these interpretations for the variables in scope
an (evaluation) environment. The content of environments may vary
wildly between different instances (e.g. renaming environments
contain variables whilst the normalisation by evaluation ones
carry elements of the model) but their structure is generic.

Formally, environments are defined as the pointwise lifting of a
relation \AB{R} between contexts and types to a relation between
two contexts.

\AgdaHide{
\begin{code}
infix 5 _[_]_
\end{code}}
\begin{code}
_[_]_ :  {ℓ : Level} (Δ : Con) (R : (Δ : Con) (σ : ty) → Set ℓ) (Γ : Con) → Set ℓ
Δ [ R ] Γ = (σ : ty) (v : σ ∈ Γ) → R Δ σ
\end{code}

\AgdaHide{
\begin{code}
infixl 10 [_]_`∙_
\end{code}}

For a fixed context \AB{Δ} and relation \AB{R}, these environments can
be built step by step by noticing that the environment corresponding to
an empty context is trivial and that one may extend and already existing
environment provided a proof of the right type.

\begin{code}
`ε : {ℓ : Level} {Δ : Con} {R : (Δ : Con) (σ : ty) → Set ℓ} → Δ [ R ] ε
`ε = λ _ ()

[_]_`∙_ :  {ℓ : Level} {Γ Δ : Con} (R : (Δ : Con) (σ : ty) → Set ℓ) {σ : ty} (ρ : Δ [ R ] Γ) (s : R Δ σ) → Δ [ R ] (Γ ∙ σ)
([ R ] ρ `∙ s) _ here!       = s
([ R ] ρ `∙ s) σ (there pr)  = ρ σ pr
\end{code}

\subsection{The Preoder of Context Inclusions}
\label{preorder}

One instance of environments which will play a predominant role
in this paper and the reader may be accustomed to is the notion
of context inclusion. A context inclusion \AB{Γ} \AF{⊆} \AB{Δ}
is an environment pairing each variable of type \AB{σ} in \AB{Γ}
to one of the same type in \AB{Δ}.

\AgdaHide{
\begin{code}
infix 5 _⊆_
\end{code}}
\begin{code}
_⊆_ : (Γ Δ : Con) → Set
Γ ⊆ Δ = Δ [ flip _∈_ ] Γ
\end{code}

Context inclusions allow for the formulation of weakening principles
explaining how to transport properties along inclusions. By a ``weakening
principle'', we mean that knowing that \AB{P} holds of \AB{Γ} and that
\AB{Γ} \AF{⊆} \AB{Δ} lets us conclude that \AB{P} holds for \AB{Δ} too.
In the case of variables, weakening merely corresponds to applying the
transport function in order to obtain a renamed variable. The case of
environments is also quite simple: being a pointwise lifting of a
relation \AB{R} between contexts and types, they enjoy weakening if
\AB{R} does.

\begin{code}
wk^∈ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) (pr : σ ∈ Γ) → σ ∈ Δ
wk^∈ inc pr = inc _ pr

wk[_] :  {ℓ : Level} {Δ : Con} {R : (Δ : Con) (σ : ty) → Set ℓ} (wk : {Θ : Con} {σ : ty} (inc : Δ ⊆ Θ) → R Δ σ → R Θ σ)
         {Γ Θ : Con} (inc : Δ ⊆ Θ) (ρ : Δ [ R ] Γ) →  Θ [ R ] Γ
wk[ wk ] inc ρ = λ σ pr → wk inc $ ρ σ pr
\end{code}

These simple observations allow us to prove that context inclusions
form a preorder which, in turn, lets us provide the user with the
constructors Altenkirch, Hofmann and Streicher's ``Category of
Weakenings"~\cite{altenkirch1995categorical} is based on.

\begin{code}
refl : {Γ : Con} → Γ ⊆ Γ
refl = λ _ → id

trans : {Γ Δ Θ : Con} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ) → Γ ⊆ Θ
trans inc₁ inc₂ = wk[ wk^∈ ] inc₂ inc₁

pop! : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) → (Γ ∙ σ) ⊆ (Δ ∙ σ)
pop! inc σ here!       = here!
pop! inc σ (there pr)  = there $ inc σ pr

step : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) → Γ ⊆ (Δ ∙ σ)
step inc = trans inc $ λ _ → there
\end{code}

Now that we are equipped with the notion of inclusion, we have all
the pieces necessary to describe the Kripke structure of our models
of the simply-typed λ-calculus.

\section{Semantics and Generic Evaluation Functions}

The upcoming sections are dedicated to demonstrating that renaming,
substitution, pretty-printing, and normalisation by evaluation all
share the same structure. We start by abstracting away a notion of
\AR{Semantics} encompassing all these constructions. This approach
will make it possible for us to implement a generic traversal
parametrised by such a \AR{Semantics} once and for all and to focus
on the interesting model constructions instead of repeating the same
pattern over and over again.

A \AR{Semantics} is indexed by two relations \AB{𝓔} and \AB{𝓜}
describing respectively the values in the environment and the ones
in the model. It packs the properties of these relations necessary
to define the evaluation function.

\begin{code}
record Semantics {ℓ^E ℓ^M : Level}
       (𝓔  : (Γ : Con) (σ : ty) → Set ℓ^E)
       (𝓜  : (Γ : Con) (σ : ty) → Set ℓ^M) : Set (ℓ^E ⊔ ℓ^M) where
\end{code}
\AgdaHide{
\begin{code}
  infixl 5 _⟦$⟧_
\end{code}}\vspace{-2.5em}%ugly but it works!
\begin{code}
  field
\end{code}

The first two methods of a \AR{Semantics} are dealing with environment
values. These values need to come with a notion of weakening (\ARF{wk})
so that the traversal may introduce fresh variables when going under a
binder and keep the environment well-scoped. We also need to be able to
manufacture environment values given a variable in scope (\ARF{embed})
in order to be able to craft a diagonal environment to evaluate an open
term.

\begin{code}
    wk      :  {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) (r : 𝓔 Γ σ) → 𝓔 Δ σ
    embed   :  {Γ : Con} (σ : ty) (pr : σ ∈ Γ) → 𝓔 Γ σ
\end{code}

The structure of the model is quite constrained: each constructor
in the language needs a semantic counterpart. We start with the
two most interesting cases: \ARF{⟦var⟧} and \ARF{⟦λ⟧}. The variable
case guarantees that one can turn a value from the environment into
one in the model thus making it possible for the traversal, when
hitting a variable, to lookup the corresponding value in the environment
and return it.

\begin{code}
    ⟦var⟧   :  {Γ : Con} {σ : ty} (v : 𝓔 Γ σ) → 𝓜 Γ σ
\end{code}

The semantic λ-abstraction is notable for two reasons: first, following
Mitchell and Moggi~\cite{mitchell1991kripke}, it has a structure typical
of Kripke style models thus allowing arbitrary extensions of the context;
and instead of being a function in the host language taking values in the
model as arguments, it is a function that takes \emph{environment} values.
This slight variation in the type of the semantic λ-abstraction is what
makes it possible to go beyond the semantics such as substitution
or normalisation by evaluation where \AB{𝓔} and \AB{𝓜} happen
to coincide.

\begin{code}
    ⟦λ⟧     :  {Γ : Con} {σ τ : ty} (t : {Δ : Con} (pr : Γ ⊆ Δ) (u : 𝓔 Δ σ) → 𝓜 Δ τ) → 𝓜 Γ (σ `→ τ)
\end{code}

The remaining fields' types are a direct translation of the types
of the constructor they correspond to where the type constructor
characterising typing derivations (\AD{\_⊢\_}) has been replaced
with the one corresponding to model values (\AB{𝓜}).

\begin{code}
    _⟦$⟧_   :  {Γ : Con} {σ τ : ty} → 𝓜 Γ (σ `→ τ) → 𝓜 Γ σ → 𝓜 Γ τ
    ⟦⟨⟩⟧    :  {Γ : Con} → 𝓜 Γ `Unit
    ⟦tt⟧    :  {Γ : Con} → 𝓜 Γ `Bool
    ⟦ff⟧    :  {Γ : Con} → 𝓜 Γ `Bool
    ⟦ifte⟧  :  {Γ : Con} {σ : ty} (b : 𝓜 Γ `Bool) (l r : 𝓜 Γ σ) → 𝓜 Γ σ
\end{code}

The fundamental lemma of semantics is then proved in a module indexed by
a \AF{Semantics}. It is defined by structural recursion on the term. Each
constructor is replaced by its semantic counterpart in order to combine the
induction hypotheses its subterms give rise to. In the λ-abstraction case,
the type of \ARF{⟦λ⟧} guarantees that the semantic argument can be stored
in the environment which will have been weakened beforehand.

\begin{code}
module Eval {ℓ^E ℓ^M : Level} {𝓔 : (Γ : Con) (σ : ty) → Set ℓ^E} {𝓜 : (Γ : Con) (σ : ty) → Set ℓ^M} (Sem : Semantics 𝓔 𝓜) where
  open Semantics Sem
\end{code}\vspace{-2.5em}%ugly but it works!
\AgdaHide{
\begin{code}
  infix 10 _⊨⟦_⟧_ _⊨eval_
\end{code}}
\begin{code}
  lemma : {Δ Γ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ 𝓔 ] Γ) → 𝓜 Δ σ
  lemma (`var v)       ρ = ⟦var⟧ $ ρ _ v
  lemma (t `$ u)       ρ = lemma t ρ ⟦$⟧ lemma u ρ
  lemma (`λ t)         ρ = ⟦λ⟧  λ inc u → lemma t $ [ 𝓔 ] wk[ wk ] inc ρ `∙ u
  lemma `⟨⟩            ρ = ⟦⟨⟩⟧
  lemma `tt            ρ = ⟦tt⟧
  lemma `ff            ρ = ⟦ff⟧
  lemma (`ifte b l r)  ρ = ⟦ifte⟧ (lemma b ρ) (lemma l ρ) (lemma r ρ)
\end{code}

We introduce \AF{\_⊨⟦\_⟧\_} as an alternative name for the fundamental
lemma and \AF{\_⊨eval\_} for the special case where we use \ARF{embed}
to generate a diagonal environment of type \AB{Γ} \AF{[} \AB{𝓔} \AF{]}
\AB{Γ}. Because we open the module \AM{Eval} without passing it a parameter
of type \AF{Semantics}, the types of its elements are all λ-lifted to include
an extra argument of such a type. This means that partial application of
\AF{\_⊨⟦\_⟧\_} will correspond to the specialisation of the fundamental
lemma to a given semantics. \AB{𝓢} \AF{⊨⟦} \AB{t} \AF{⟧} \AB{ρ} is
meant to convey the idea that the semantics \AB{𝓢} is used to evaluate
the term \AB{t} in the environment \AB{ρ}. Similarly, \AB{𝓢} \AF{⊨eval}
\AB{t} is meant to denote the evaluation of the term \AB{t} in the semantics
\AB{𝓢} (using a diagonal environment).

\begin{code}
  _⊨⟦_⟧_ : {Δ Γ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ 𝓔 ] Γ) → 𝓜 Δ σ
  _⊨⟦_⟧_ = lemma

  _⊨eval_ : {Γ : Con} {σ : ty} (t : Γ ⊢ σ) → 𝓜 Γ σ
  _⊨eval_ t = _⊨⟦_⟧_ t embed

open Eval hiding (lemma) public
\end{code}

The diagonal environment generated using \ARF{embed} when defining the
\AF{\_⊨eval\_} function lets us kickstart the evaluation of arbitrary
\emph{open} terms. In the case of pretty-printing, this corresponds to
picking a naming scheme for free variables whilst in the usual model
construction used to perform normalisation by evaluation, it corresponds
to η-expanding the variables.

\section{Syntactic Semantics}

As we have explained earlier, this work has been directly influenced by
McBride's functional pearl~\cite{mcbride2005type}. It seems appropriate
to start our exploration of \AR{Semantics} with the two operations he
implements with a single traversal. We call these operations syntactic
because the values in the model are actual terms and almost all term
constructors are kept as their own semantic counterpart. As observed by
McBride, it is enough to provide three operations describing the properties
of the values in the environment to get a full-blown \AR{Semantics}. This
fact is witnessed by our simple \AR{Syntactic} record type together with
the \AF{syntactic} function turning its inhabitants into associated
\AR{Semantics}.

\begin{code}
record Syntactic {ℓ : Level} (𝓔 : (Γ : Con) (σ : ty) → Set ℓ) : Set ℓ where
  field
    embed  : {Γ : Con} (σ : ty) (pr : σ ∈ Γ) → 𝓔 Γ σ
    wk     : {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) → 𝓔 Γ σ → 𝓔 Δ σ
    ⟦var⟧  : {Γ : Con} {σ : ty} (v : 𝓔 Γ σ) → Γ ⊢ σ

syntactic : {ℓ : Level} {𝓔 : (Γ : Con) (σ : ty) → Set ℓ} (syn : Syntactic 𝓔) → Semantics 𝓔 _⊢_
syntactic syn =
  let open Syntactic syn in
  record  { wk      = wk
          ; embed   = embed
          ; ⟦var⟧   = ⟦var⟧
          ; _⟦$⟧_   = _`$_
          ; ⟦λ⟧     = λ t → `λ $ t (step refl) $ embed _ here!
          ; ⟦⟨⟩⟧    = `⟨⟩
          ; ⟦tt⟧    = `tt
          ; ⟦ff⟧    = `ff
          ; ⟦ifte⟧  = `ifte
          }
\end{code}

The shape of \ARF{⟦λ⟧} or \ARF{⟦⟨⟩⟧} should not trick the reader
into thinking that this definition performs some sort of η-expansion:
\AF{lemma} indeed only ever uses one of these when the evaluated term's
head constructor is already respectively a \AIC{`λ} or a \AIC{`⟨⟩}.
It is therefore absolutely possible to define renaming or substitution
using this approach. We can now port McBride's definitions to our
framework.

\subsection{Functoriality, also known as Renaming}

Our first example of a \AR{Syntactic} operation works with variables as
environment values. As a consequence, embedding is trivial; we have already
defined weakening earlier (see Section \ref{preorder}) and we can turn
a variable into a term by using the \AIC{`var} constructor.

\begin{code}
syntacticRenaming : Syntactic (flip _∈_)
syntacticRenaming =
  record  { embed  = λ _ → id
          ; wk     = wk^∈
          ; ⟦var⟧  = `var }

Renaming : Semantics (flip _∈_) _⊢_
Renaming = syntactic syntacticRenaming
\end{code}

We obtain a rather involved definition of the identity of type \AB{Γ}
\AD{⊢} \AB{σ} \AS{→} \AB{Γ} \AD{⊢} \AB{σ} as \AF{Renaming} \AF{⊨eval\_}.
But this construction is not at all useless: indeed, the more general
\AF{Renaming} \AF{⊨⟦\_⟧\_} function has type \AB{Γ} \AD{⊢} \AB{σ} \AS{→}
\AB{Γ} \AF{⊆} \AB{Δ} \AS{→} \AB{Δ} \AD{⊢} \AB{σ} which turns out to be
precisely the notion of weakening for terms we need once its arguments
have been flipped.

\begin{code}
wk^⊢ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) (t : Γ ⊢ σ) → Δ ⊢ σ
wk^⊢ = flip $ Renaming ⊨⟦_⟧_
\end{code}

\subsection{Parallel Substitution}

Our second example of a semantics is another spin on the syntactic model:
the environment values are now terms. We can embed variables into environment
values by using the \AIC{`var} constructor and we inherit weakening for terms
from the previous example.

\begin{code}
syntacticSubstitution : Syntactic _⊢_
syntacticSubstitution =
  record  { embed   = λ _ → `var
          ; wk      = wk^⊢
          ; ⟦var⟧   = id
          }

Substitution : Semantics _⊢_ _⊢_
Substitution = syntactic syntacticSubstitution
\end{code}

Because the diagonal environment used by \AF{Substitution} \AF{⊨eval\_}
is obtained by \ARF{embed}ding membership proofs into terms using the
\AIC{`var} constructor, we get yet another definition of the identity
function on terms. The semantic function \AF{Substitution} \AF{⊨⟦\_⟧\_}
is again more interesting: it is an implementation of parallel substitution.

\begin{code}
subst : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊢_ ] Γ) → Δ ⊢ σ
subst = Substitution ⊨⟦_⟧_
\end{code}

\section{Pretty Printing}

Before considering the various model constructions involved in defining
normalisation functions deciding different equational theories, let us
make a detour to a perhaps slightly more surprising example of a
\AF{Semantics}: Pretty Printing. This example is quite interesting for
two reasons: it is another instance of a \AR{Semantics} where values in
the environment and values in the model have a different type, and for
the first time in this paper, the values in the model are monadic.

Firstly, the distinction between the type of values in the environment and
the ones in the model is once more instrumental in giving the procedure a
precise type guiding our implementation. Indeed, the environment carries
\emph{names} for the variables currently in scope whilst the inhabitants of
the model are \emph{computations} threading a stream to be used as a source
of fresh names every time a new variable is introduced by a λ-abstraction.

\AgdaHide{
\begin{code}
open import Data.Char using (Char)
open import Data.String hiding (show)
open import Data.Nat as ℕ using (ℕ ; _+_)
open import Data.Nat.Show
open import Data.List as List hiding (_++_ ; zipWith ; [_])
open import Coinduction
open import Data.Stream as Stream using (Stream ; head ; tail ; zipWith ; _∷_)
open import Category.Monad
open import Category.Monad.State
open RawIMonadState (StateMonadState (Stream String)) hiding (zipWith ; pure)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
\end{code}
}

\begin{code}
Names : (Γ : Con) (σ : ty) → Set
Names _ _ = String

Printer : (Γ : Con) (σ : ty) → Set
Printer _ _ = State (Stream String) String
\end{code}

If the values in the environment were allowed to be computations too, we
would not root out all faulty implementations: the typechecker would for
instance quite happily accept a program picking a new name every time a
variable appears in the term.

Secondly, the fact that values in the model are computations and that this
poses no problem whatsoever in this framework means it is appropriate for
handling languages with effects~\cite{moggi1991notions}, or effectful
semantics (e.g. logging the various function calls).

\begin{code}
PrettyPrinting : Semantics Names Printer
PrettyPrinting =
  record  { embed   = λ _ → show ∘ deBruijn
          ; wk      = λ _ → id
          ; ⟦var⟧   = return
          ; _⟦$⟧_   = λ  mf mt →
                         mf  >>= λ `f` →
                         mt  >>= λ `t` →
                         return $ `f` ++ "(" ++ `t` ++ ")"
          ; ⟦λ⟧     = λ  {_} {σ} mb →
                         get                         >>= λ names →
                         let `x`   = head names
                             rest  = tail names in
                         put rest                    >>= λ _ →
                         mb (step {σ = σ} refl) `x`  >>= λ `b` →
                         return $ "λ" ++ `x` ++ ". " ++ `b`
          ; ⟦⟨⟩⟧    = return "⟨⟩"
          ; ⟦tt⟧    = return "tt"
          ; ⟦ff⟧    = return "ff"
          ; ⟦ifte⟧  = λ  mb ml mr →
                         mb  >>= λ `b` →
                         ml  >>= λ `l` →
                         mr  >>= λ `r` →
                         return  $ "if (" ++ `b` ++ ") "
                                 ++ "then (" ++ `l` ++ ") "
                                 ++ "else (" ++ `r` ++ ")"
          }
\end{code}

Our definition of \ARF{embed} erases the membership proofs to
recover the corresponding de Bruijn indices which are then turned
into strings using \AF{show}, defined in Agda's standard library.
This means that, using \AF{PrettyPrinting} \AF{⊨eval\_}, the free
variables will be displayed as numbers whilst the bound ones will
be given names chosen by the name supply.

\begin{code}
  where
    deBruijn : {Γ : Con} {σ : ty} → σ ∈ Γ → ℕ
    deBruijn here!       = 0
    deBruijn (there pr)  = 1 + deBruijn pr
\end{code}

Now, this means that we still need to provide a \AD{Stream} of fresh
names to this computation in order to run it. Given that we erase free
variables to numbers, we'd rather avoid using numbers if we want to
avoid capture. We define \AF{names} (not shown here) as the stream
cycling through the letters of the alphabet and keeping the identifiers
unique by appending a natural number incremented by 1 each time we are
back to the beginning of the cycle.

\AgdaHide{
\begin{code}
flatten : {A : Set} → Stream (A × List A) → Stream A
flatten ((a , as) ∷ aass) = go a as (♭ aass) where
  go : {A : Set} → A → List A → Stream (A × List A) → Stream A
  go a []        aass = a ∷ ♯ flatten aass
  go a (b ∷ as)  aass = a ∷ ♯ go b as aass

names : Stream String
names = flatten $ zipWith cons letters $ "" ∷ ♯ Stream.map show (allNatsFrom 0)
  where
    cons : (Char × List Char) → String → (String × List String)
    cons (c , cs) suffix = appendSuffix c , map appendSuffix cs where
      appendSuffix : Char → String
      appendSuffix c  = fromList (c ∷ []) ++ suffix

    letters = Stream.repeat $ 'a' , toList "bcdefghijklmnopqrstuvwxyz"

    allNatsFrom : ℕ → Stream ℕ
    allNatsFrom k = k ∷ ♯ allNatsFrom (1 + k)
\end{code}}
\begin{code}
prettyPrint : {Γ : Con} {σ : ty} (t : Γ ⊢ σ) → String
prettyPrint t = proj₁ $ PrettyPrinting ⊨eval t $ names
\end{code}

We can observe that \AF{prettyPrint} does indeed do the job by writing a
test. Given that type theory allows computation at the type level, we can
make sure that such tests are checked at typechecking time. Here we display
a function applying its argument to the first free variable in scope. The
free variable is indeed given a natural number as a name whilst the bound
one uses a letter.

\begin{code}
pretty$ :  {a b : ty} → prettyPrint {Γ = ε ∙ a `→ b} {σ = a `→ b} (`λ $ `var (there here!) `$ `var here!) ≡ "λa. 0(a)"
pretty$ = PEq.refl
\end{code}

\section{Normalisation by Evaluation}

Normalisation by Evaluation is a technique leveraging the computational
power of a host language in order to normalise expressions of a deeply
embedded one. The process is based on a model construction associating
a type of values \model{} to each context \AB{Γ} and type \AB{σ}. Two
procedures are then defined: the first one (\AF{eval}) produces elements
of \model{} provided a well-typed term of the corresponding \AB{Γ} \AD{⊢}
\AB{σ} type and an interpretation for the variables in \AB{Γ} whilst
the second one (\AF{reify}) extracts, in a type-directed manner, normal
forms \AB{Γ} \AD{⊢^{nf}} \AB{σ} from elements of the model \model{}.
Normalisation is achieved by composing the two procedures.

The definition of this \AF{eval} function is a natural candidate for our
\AF{Semantics} framework. Normalisation is always defined for a given
equational theory so we are going to start by recalling the various
rules a theory may satisfy.

\paragraph{β-rule} Using the \AF{Substitution} \AF{Semantics}, we can
describe β-reduction in the usual manner.

\begin{mathpar}
\inferrule{
  }{\text{(\AIC{`λ} \AB{t}) \AIC{`\$} \AB{u} ↝ \AB{t} \AF{⟨} \AB{u} \AF{/var₀⟩}}
  }{β}
\end{mathpar}
\AgdaHide{
\begin{code}
infixl 10 _⟨_/var₀⟩
\end{code}}
\begin{code}
_⟨_/var₀⟩ : {Γ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
t ⟨ u /var₀⟩ = subst t $ [ _⊢_ ] (λ _ → `var) `∙ u
\end{code}

\paragraph{ι-rule} The presence of an inductive data type (\AIC{`Bool})
and its eliminator (\AIC{`ifte}) means we have an extra opportunity for
computations to happen when the boolean the eliminator is branching
over is in canonical form.

\begin{mathpar}
\inferrule{
  }{\text{\AIC{`ifte} \AIC{`tt} \AB{l} \AB{r} ↝ \AB{l}}
  }{ι_1}
\and
\inferrule{
  }{\text{\AIC{`ifte} \AIC{`ff} \AB{l} \AB{r} ↝ \AB{r}}
  }{ι_2}
\end{mathpar}

\paragraph{ξ-rule} The ξ-rule is what makes the distinction between
strong normalisation and weak head normalisation. It allows reductions
to take place under lambdas.

\begin{mathpar}
\inferrule{\text{\AB{t} ↝ \AB{u}}
  }{\text{\AIC{`λ} \AB{t} ↝ \AIC{`λ} \AB{u}}
  }{ξ}
\end{mathpar}

\paragraph{η-rule} Finally the η-rules are saying that for some types,
terms have a canonical form: functions will all be λ-headed whilst
record will be a collection of fields which translates here to all
the elements of the \AIC{`Unit} type being equal to \AIC{`⟨⟩}.

\begin{mathpar}
\inferrule{
  }{\text{\AB{t} ↝ \AF{eta} \AB{t}}
  }{η_1}
\and
\inferrule{\text{\AB{t} \AgdaSymbol{:} \AB{Γ} \AD{⊢} \AIC{`Unit}}
  }{\text{\AB{t} ↝ \AIC{`⟨⟩}}
  }{η_2}
\end{mathpar}
\begin{code}
eta : {Γ : Con} {σ τ : ty} (t : Γ ⊢ σ `→ τ) → Γ ⊢ σ `→ τ
eta t = `λ $ wk^⊢ (step refl) t `$ `var here!
\end{code}

Now that we have recalled all these rules, we can talk precisely
about the sort of equational theory decided by the model construction
we choose to perform. We start with the usual definition of Normalisation
by Evaluation which goes under λs and produces η-long βι-short normal
forms.

\subsection{Normalisation by Evaluation for βιξη}
\label{nbe}

These η-long βι-short normal forms can be formally described by two
mutually defined inductive families: \AD{\_⊢^{ne}\_} is the type of
stuck terms made up of a variable to which a spine of eliminators in
normal forms is applied; and \AD{\_⊢^{nf}\_} describes these normal
forms.

\AgdaHide{
\begin{code}
infix 5 _⊢^ne_ _⊢^nf_
\end{code}}
\begin{code}
mutual

  data _⊢^ne_ (Γ : Con) (σ : ty) : Set where
    `var   : (v : σ ∈ Γ) → Γ ⊢^ne σ
    _`$_   : {τ : ty} (t : Γ ⊢^ne τ `→ σ) (u : Γ ⊢^nf τ) → Γ ⊢^ne σ
    `ifte  : (b : Γ ⊢^ne `Bool) (l r : Γ ⊢^nf σ) → Γ ⊢^ne σ

  data _⊢^nf_ (Γ : Con) : (σ : ty) → Set where
    `embed  : {σ : ty} (t : Γ ⊢^ne σ) → Γ ⊢^nf σ
    `⟨⟩     : Γ ⊢^nf `Unit
    `tt     : Γ ⊢^nf `Bool
    `ff     : Γ ⊢^nf `Bool
    `λ      : {σ τ : ty} (b : Γ ∙ σ ⊢^nf τ) → Γ ⊢^nf σ `→ τ
\end{code}

Once more, context inclusions induce a notion of weakening. We hide
the purely structural definition of \AF{wk^{ne}} and \AF{wk^{nf}}
but quickly recall their respective types:

\begin{code}
wk^ne : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^ne σ) → Δ ⊢^ne σ
wk^nf : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^nf σ) → Δ ⊢^nf σ
\end{code}
\AgdaHide{
\begin{code}
wk^ne inc (`var v)        = `var $′ wk^∈ inc v
wk^ne inc (ne `$ u)       = wk^ne inc ne `$ wk^nf inc u
wk^ne inc (`ifte ne l r)  = `ifte (wk^ne inc ne) (wk^nf inc l) (wk^nf inc r)

wk^nf inc (`embed t)  = `embed $′ wk^ne inc t
wk^nf inc `⟨⟩         = `⟨⟩
wk^nf inc `tt         = `tt
wk^nf inc `ff         = `ff
wk^nf inc (`λ nf)     = `λ $′ wk^nf (pop! inc) nf

infix 5 [_,_]
[_,_] : {Γ : Con} {τ : ty} {P : (σ : ty) (pr : σ ∈ Γ ∙ τ) → Set} →
        (p0 : P τ here!) →
        (pS : (σ : ty) (pr : σ ∈ Γ) → P σ (there pr)) →
        (σ : ty) (pr : σ ∈ Γ ∙ τ) → P σ pr
[ p0 , pS ] σ here!       = p0
[ p0 , pS ] σ (there pr)  = pS σ pr

mutual

  wk^nf-refl′ : {Γ : Con} {σ : ty} {f : Γ ⊆ Γ} (prf : (σ : ty) (pr : σ ∈ Γ) → f σ pr ≡ pr) →
                (t : Γ ⊢^nf σ) → wk^nf f t ≡ t
  wk^nf-refl′ prf (`embed t)  = PEq.cong `embed $ wk^ne-refl′ prf t
  wk^nf-refl′ prf `⟨⟩         = PEq.refl
  wk^nf-refl′ prf `tt         = PEq.refl
  wk^nf-refl′ prf `ff         = PEq.refl
  wk^nf-refl′ prf (`λ t)      = PEq.cong `λ $ wk^nf-refl′ ([ PEq.refl , (λ σ → PEq.cong there ∘ prf σ) ]) t

  wk^ne-refl′ : {Γ : Con} {σ : ty} {f : Γ ⊆ Γ} (prf : (σ : ty) (pr : σ ∈ Γ) → f σ pr ≡ pr) →
                (t : Γ ⊢^ne σ) → wk^ne f t ≡ t
  wk^ne-refl′ prf (`var v)       = PEq.cong `var $ prf _ v
  wk^ne-refl′ prf (t `$ u)       = PEq.cong₂ _`$_ (wk^ne-refl′ prf t) (wk^nf-refl′ prf u)
  wk^ne-refl′ prf (`ifte b l r)  = PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ (wk^ne-refl′ prf b) (wk^nf-refl′ prf l)) (wk^nf-refl′ prf r)

mutual

  wk^nf-trans′ : {Θ Δ Γ : Con} {σ : ty} {inc₁ : Γ ⊆ Δ} {inc₂ : Δ ⊆ Θ}
                 {f : Γ ⊆ Θ} (prf : (σ : ty) (pr : σ ∈ Γ) → trans inc₁ inc₂ σ pr ≡ f σ pr)
                 (t : Γ ⊢^nf σ) →  wk^nf inc₂ (wk^nf inc₁ t) ≡ wk^nf f t
  wk^nf-trans′ prf (`embed t)  = PEq.cong `embed (wk^ne-trans′ prf t)
  wk^nf-trans′ prf `⟨⟩         = PEq.refl
  wk^nf-trans′ prf `tt         = PEq.refl
  wk^nf-trans′ prf `ff         = PEq.refl
  wk^nf-trans′ prf (`λ t)      = PEq.cong `λ $ wk^nf-trans′ ([ PEq.refl , (λ σ → PEq.cong there ∘ prf σ) ]) t

  wk^ne-trans′ : {Θ Δ Γ : Con} {σ : ty} {inc₁ : Γ ⊆ Δ} {inc₂ : Δ ⊆ Θ}
                 {f : Γ ⊆ Θ} (prf : (σ : ty) (pr : σ ∈ Γ) → trans inc₁ inc₂ σ pr ≡ f σ pr)
                 (t : Γ ⊢^ne σ) →  wk^ne inc₂ (wk^ne inc₁ t) ≡ wk^ne f t
  wk^ne-trans′ prf (`var v)       = PEq.cong `var (prf _ v)
  wk^ne-trans′ prf (t `$ u)       = PEq.cong₂ _`$_ (wk^ne-trans′ prf t) (wk^nf-trans′ prf u)
  wk^ne-trans′ prf (`ifte b l r)  = PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ (wk^ne-trans′ prf b) (wk^nf-trans′ prf l)) (wk^nf-trans′ prf r)

wk^nf-refl : {Γ : Con} {σ : ty} (t : Γ ⊢^nf σ) → wk^nf refl t ≡ t
wk^nf-refl = wk^nf-refl′ (λ _ _ → PEq.refl)

wk^ne-refl : {Γ : Con} {σ : ty} (t : Γ ⊢^ne σ) → wk^ne refl t ≡ t
wk^ne-refl = wk^ne-refl′ (λ _ _ → PEq.refl)

wk^nf-trans : {Θ Δ Γ : Con} {σ : ty} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ)
               (t : Γ ⊢^nf σ) →  wk^nf inc₂ (wk^nf inc₁ t) ≡ wk^nf (trans inc₁ inc₂) t
wk^nf-trans inc₁ inc₂ = wk^nf-trans′ (λ _ _ → PEq.refl)

wk^ne-trans : {Θ Δ Γ : Con} {σ : ty} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ)
               (t : Γ ⊢^ne σ) →  wk^ne inc₂ (wk^ne inc₁ t) ≡ wk^ne (trans inc₁ inc₂) t
wk^ne-trans inc₁ inc₂ = wk^ne-trans′ (λ _ _ → PEq.refl)
\end{code}}

We now come to the definition of the model which follows the usual pattern
pioneered by Berger~\cite{berger1993program} and formally explained in great
details by e.g. Catarina Coquand~\cite{coquand2002formalised}. We proceed by
induction on the type and make sure that η-expansion is applied eagerly: all
inhabitants of \AB{Γ} \AF{⊨^βιξη} \AIC{`Unit} are indeed equal and all elements
of \AB{Γ} \AF{⊨^βιξη} (\AB{σ} \AIC{`→} \AB{τ}) are functions in Agda meaning
that their reifications will be guaranteed to be \AIC{`λ}-headed.

\AgdaHide{
\begin{code}
infix 5 _⊨^βιξη_
\end{code}}
\begin{code}
_⊨^βιξη_ : (Γ : Con) (σ : ty) → Set
Γ ⊨^βιξη `Unit   = ⊤
Γ ⊨^βιξη `Bool   = Γ ⊢^nf `Bool
Γ ⊨^βιξη σ `→ τ  = {Δ : Con} (inc : Γ ⊆ Δ) (u : Δ ⊨^βιξη σ) → Δ ⊨^βιξη τ
\end{code}

Normal forms may be weakened, and context inclusions may be composed hence
the rather simple definition of weakening for inhabitants of the model.

\begin{code}
wk^βιξη : {Δ Γ : Con} (σ : ty) (inc : Γ ⊆ Δ) (T : Γ ⊨^βιξη σ) → Δ ⊨^βιξη σ
wk^βιξη `Unit     inc T = T
wk^βιξη `Bool     inc T = wk^nf inc T
wk^βιξη (σ `→ τ)  inc T = λ inc′ → T $′ trans inc inc′
\end{code}

The semantic counterpart of application combines two elements of the model:
a functional part of type \AB{Γ} \AF{⊨^{βιξη}} \AS{(}\AB{σ} \AIC{`→} \AB{τ}\AS{)}
and its argument of type \AB{Γ} \AF{⊨^{βιξη}} \AB{σ} which can be fed to the
functional given a proof that \AB{Γ} \AF{⊆} \AB{Γ}. But we already have
proven that \AF{\_⊆\_} is a preorder (see Section ~\ref{preorder}) so this
is not at all an issue.

\AgdaHide{
\begin{code}
infixr 5 _$^βιξη_
\end{code}}
\begin{code}
_$^βιξη_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βιξη σ `→ τ) (u : Γ ⊨^βιξη σ) → Γ ⊨^βιξη τ
t $^βιξη u = t refl u
\end{code}

Conditional Branching on the other hand is a bit more subtle: because the boolean
value \AIC{`ifte} is branching over may be a neutral term, we are forced to define
the reflection and reification mechanisms first. These functions, also known as
unquote and quote respectively, are showing the interplay between neutral terms,
model values and normal forms. \AF{reflect^{βιξη}} performs a form semantical
η-expansion: all stuck \AIC{`Unit} terms are projected to the same element \AIC{tt},
and all stuck functions are turned into functions in the host language.

\begin{code}
mutual

  var‿0^βιξη : {Γ : Con} {σ : ty} → Γ ∙ σ ⊨^βιξη σ
  var‿0^βιξη = reflect^βιξη _ $′ `var here!

  reflect^βιξη : {Γ : Con} (σ : ty) (t : Γ ⊢^ne σ) → Γ ⊨^βιξη σ
  reflect^βιξη `Unit     t = tt
  reflect^βιξη `Bool     t = `embed t
  reflect^βιξη (σ `→ τ)  t = λ inc u → reflect^βιξη τ $′ wk^ne inc t `$ reify^βιξη σ u

  reify^βιξη : {Γ : Con} (σ : ty) (T : Γ ⊨^βιξη σ) → Γ ⊢^nf σ
  reify^βιξη `Unit     T = `⟨⟩
  reify^βιξη `Bool     T = T
  reify^βιξη (σ `→ τ)  T = `λ $′ reify^βιξη τ $′ T (step refl) var‿0^βιξη
\end{code}

The semantic counterpart of \AIC{`ifte} can then be defined: if the boolean
is a value, the appropriate branch is picked and if it is stuck the whole
expression is reflected in the model.

\begin{code}
ifte^βιξη : {Γ : Con} {σ : ty} (b : Γ ⊨^βιξη `Bool) (l r : Γ ⊨^βιξη σ) → Γ ⊨^βιξη σ
ifte^βιξη `tt         l r = l
ifte^βιξη `ff         l r = r
ifte^βιξη (`embed T)  l r = reflect^βιξη _ $′ `ifte T (reify^βιξη _ l) (reify^βιξη _ r)
\end{code}

The \AF{Semantics} corresponding to Normalisation by Evaluation for βιξη-rules
uses \AF{\_⊨^βιξη\_} for values in the environment as well as the ones in the
model. The semantic counterpart of a λ-abstraction is simply the identity: the
structure of the functional case in the definition of the model matches precisely
the shape expected in a \AF{Semantics}. Because the environment carries model values,
the variable case simply returns the value it is given.

\begin{code}
Normalise^βιξη : Semantics _⊨^βιξη_ _⊨^βιξη_
Normalise^βιξη =
  record  { embed   = λ σ → reflect^βιξη σ ∘ `var
          ; wk      = wk^βιξη _
          ; ⟦var⟧   = id
          ; _⟦$⟧_   = _$^βιξη_
          ; ⟦λ⟧     = id
          ; ⟦⟨⟩⟧    = tt
          ; ⟦tt⟧    = `tt
          ; ⟦ff⟧    = `ff
          ; ⟦ifte⟧  = ifte^βιξη
          }
\end{code}

The diagonal environment built up in \AF{Normalise^βιξη} \AF{⊨eval\_}
consists of η-expanded variables. Normalisation is obtained by reifying
the result obtained by evaluation.

\begin{code}
norm^βιξη : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^nf σ
norm^βιξη σ t = reify^βιξη σ $′ Normalise^βιξη ⊨eval t
\end{code}

\subsection{Normalisation by Evaluation for βιξ}

As we have just seen, the traditional typed model construction leads to a
normalisation procedure outputting βι-normal η-long terms. However evaluation
strategies implemented in actual proof systems tend to avoid applying η-rules
as much as possible: quite unsurprisingly, when typechecking complex developments
expanding the proof terms is a really bad idea. Garillot and colleagues~\cite{garillot2009packaging}
report that common mathematical structures packaged in records can lead to terms
of such a size that theorem proving becomes impractical.

In these systems, normal forms are neither η-long nor η-short: the η-rule is
actually never considered except when comparing two terms for equality, one of
which is neutral whilst the other is constructor-headed. Instead of declaring
them to be distinct, the algorithm will perform one step of η-expansion on the
neutral term and keep comparing their subterms structurally. The conversion test
will only fail when confronted with two neutral terms which have distinct head
variables or two normal forms with distinct head constructors.

To reproduce this behaviour, the normalisation procedure needs to be amended.
It is possible to alter the model definition described earlier so that it
avoids unnecessary η-expansions. We proceed by enriching the traditional
model with extra syntactical artefacts in a manner reminiscent of Coquand
and Dybjer's approach to defining a Normalisation by Evaluation procedure
for the SK combinator calculus~\cite{CoqDybSK}. Their resorting to glueing
terms to elements of the model was dictated by the sheer impossibily to write
a sensible reification procedure but, in hindsight, it provides us with a
powerful technique to build models internalizing alternative equational
theories. This leads us to mutually defining the model (\AF{\_⊨^{βιξ}\_})
together with the \emph{acting} model (\AF{\_⊨^{βιξ⋆}\_}):

\AgdaHide{
\begin{code}
infix 5 _⊨^βιξ_ _⊨^βιξ⋆_
\end{code}}
\begin{code}
mutual

  _⊨^βιξ_   : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βιξ σ  = Γ ⊢^ne σ ⊎ Γ ⊨^βιξ⋆ σ

  _⊨^βιξ⋆_  : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βιξ⋆ `Unit   = ⊤
  Γ ⊨^βιξ⋆ `Bool   = Bool
  Γ ⊨^βιξ⋆ σ `→ τ  = {Δ : Con} (inc : Γ ⊆ Δ) (u : Δ ⊨^βιξ σ) → Δ ⊨^βιξ τ
\end{code}

These mutual definitions allow us to make a careful distinction between values
arising from (non expanded) stuck terms and the ones wich are constructor headed
and have a computational behaviour associated to them. The values in the acting
model are storing these behaviours be it either actual proofs of \AF{⊤}, actual
\AF{Bool}eans or actual Agda functions depending on the type of the term. It is
important to note that the functions in the acting model have the model as both
domain and codomain: there is no reason to exclude the fact that both the argument
or the body may or may not be stuck.

The definition of weakening for these structures is rather straightforward
albeit slightly more complex than for the usual definition of Normalisation
by Evaluation seen in Section ~\ref{nbe}.

\begin{code}
wk^βιξ⋆ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (T : Γ ⊨^βιξ⋆ σ) → Δ ⊨^βιξ⋆ σ
wk^βιξ⋆ inc {`Unit   } T = T
wk^βιξ⋆ inc {`Bool   } T = T
wk^βιξ⋆ inc {σ `→ τ  } T = λ inc′ → T $′ trans inc inc′

wk^βιξ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) (T : Γ ⊨^βιξ σ) → Δ ⊨^βιξ σ
wk^βιξ inc (inj₁ ne)  = inj₁ $ wk^ne inc ne
wk^βιξ inc (inj₂ T)   = inj₂ $ wk^βιξ⋆ inc T
\end{code}

What used to be called reflection in the previous model is now trivial:
stuck terms are indeed perfectly valid model values. Reification becomes
quite straightforward too because no η-expansion is needed. When facing
a stuck term, we simply embed it in the set of normal forms. Even though
\AF{reify^{βιξ⋆}} may look like it is performing some η-expansions, it
is not the case: all the values in the acting model are notionally obtained
from constructor-headed terms.

\begin{code}
reflect^βιξ : {Γ : Con} (σ : ty) (t : Γ ⊢^ne σ) → Γ ⊨^βιξ σ
reflect^βιξ σ = inj₁

mutual

  reify^βιξ⋆ : {Γ : Con} (σ : ty) (T : Γ ⊨^βιξ⋆ σ) → Γ ⊢^nf σ
  reify^βιξ⋆ `Unit     T = `⟨⟩
  reify^βιξ⋆ `Bool     T = if T then `tt else `ff
  reify^βιξ⋆ (σ `→ τ)  T = `λ $′ reify^βιξ τ $′ T (step refl) var‿0^βιξ
    where var‿0^βιξ = inj₁ $ `var here!

  reify^βιξ : {Γ : Con} (σ : ty) (T : Γ ⊨^βιξ σ) → Γ ⊢^nf σ
  reify^βιξ σ (inj₁ ne)  = `embed ne
  reify^βιξ σ (inj₂ T)   = reify^βιξ⋆ σ T
\end{code}

Semantic application is slightly more interesting: we have to dispatch
depending on whether the function is a stuck term or not. In case it is,
we can reify the argument thus growing the spine of the stuck term.
Otherwise we have an Agda function ready to be applied and we do just
that. We proceed similarly for the definition of the semantical ``if then
else''.

\AgdaHide{
\begin{code}
infixr 5 _$^βιξ_
\end{code}}
\begin{code}
_$^βιξ_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βιξ σ `→ τ) (u : Γ ⊨^βιξ σ) → Γ ⊨^βιξ τ
(inj₁ ne)  $^βιξ u = inj₁ $ ne `$ reify^βιξ _ u
(inj₂ F)   $^βιξ u = F refl u

ifte^βιξ : {Γ : Con} {σ : ty} (b : Γ ⊨^βιξ `Bool) (l r : Γ ⊨^βιξ σ) → Γ ⊨^βιξ σ
ifte^βιξ (inj₁ ne) l r = inj₁ $ `ifte ne (reify^βιξ _ l) (reify^βιξ _ r)
ifte^βιξ (inj₂ T)  l r = if T then l else r
\end{code}

Finally, we have all the components necessary to show that evaluating
the term whilst abstaining from η-expanding all stuck terms is a
perfectly valid \AR{Semantics}. As usual, normalisation is defined
by composing reification and evaluation on the diagonal environment.

\begin{code}
Normalise^βιξ : Semantics _⊨^βιξ_ _⊨^βιξ_
Normalise^βιξ =
  record  { embed   = λ σ → reflect^βιξ σ ∘ `var
          ; wk      = wk^βιξ
          ; ⟦var⟧   = id
          ; _⟦$⟧_   = _$^βιξ_
          ; ⟦λ⟧     = inj₂
          ; ⟦⟨⟩⟧    = inj₂ tt
          ; ⟦tt⟧    = inj₂ true
          ; ⟦ff⟧    = inj₂ false
          ; ⟦ifte⟧  = ifte^βιξ
          }

norm^βιξ : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^nf σ
norm^βιξ σ t = reify^βιξ σ $′ Normalise^βιξ ⊨eval t
\end{code}

\subsection{Normalisation by Evaluation for βι}

The decision to lazily apply the η-rule can be pushed further: one may
forgo using the ξ-rule and simply perform weak-head normalisation. This
leads to pursuing the computation only when absolutely necessary e.g.
when the two terms compared for equality have matching head constructors
and one needs to inspect these constructors' arguments to conclude. For
that purpose, we introduce an inductive family describing terms in weak-head
normal forms. Naturally, it is possible to define weakening for these as
well as erasure functions \AF{erase^whnf} and \AF{erase^whne} targetting
\AD{\_⊢\_} (their rather simple definitions are omitted here).

\begin{code}
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

wk^whne : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^whne σ) → Δ ⊢^whne σ
wk^whnf : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^whnf σ) → Δ ⊢^whnf σ
\end{code}
\AgdaHide{
\begin{code}
wk^whne inc (`var v)        = `var $′ wk^∈ inc v
wk^whne inc (ne `$ u)       = wk^whne inc ne `$ wk^⊢ inc u
wk^whne inc (`ifte ne l r)  = `ifte (wk^whne inc ne) (wk^⊢ inc l) (wk^⊢ inc r)

wk^whnf inc (`embed t)  = `embed $′ wk^whne inc t
wk^whnf inc `⟨⟩         = `⟨⟩
wk^whnf inc `tt         = `tt
wk^whnf inc `ff         = `ff
wk^whnf inc (`λ b)      = `λ $′ wk^⊢ (pop! inc) b

erase^whne : {Γ : Con} {σ : ty} (t : Γ ⊢^whne σ) → Γ ⊢ σ
erase^whne (`var v)       = `var v
erase^whne (t `$ u)       = erase^whne t `$ u
erase^whne (`ifte t l r)  = `ifte (erase^whne t) l r

infix 5 _⊨^βι_ _⊨^βι⋆_
\end{code}}

The model construction is quite similar to the previous one except
that source terms are now stored in the model. This means that from
an element of the model, one can pick either the reduced version of
the original term (i.e. a stuck term or the term's computational
content) or the original term itself. We exploit this ability most
notably at reification time where once we have obtained either a
head constructor (respectively a head variable), none of the subterms
need to be evaluated.

\begin{code}
mutual

  _⊨^βι_ : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βι σ  = Γ ⊢ σ  × (Γ ⊢^whne σ ⊎ Γ ⊨^βι⋆ σ)

  _⊨^βι⋆_ : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βι⋆ `Unit   = ⊤
  Γ ⊨^βι⋆ `Bool   = Bool
  Γ ⊨^βι⋆ σ `→ τ  = {Δ : Con} (inc : Γ ⊆ Δ) (u : Δ ⊨^βι σ) → Δ ⊨^βι τ
\end{code}

Once more, weakening is definable. Reflection of weak-head neutrals
is made possible by an easy lemma showing that erasure to terms is
possible.

\begin{code}
wk^βι⋆ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (T : Γ ⊨^βι⋆ σ) → Δ ⊨^βι⋆ σ
wk^βι⋆ inc {`Unit   } T = T
wk^βι⋆ inc {`Bool   } T = T
wk^βι⋆ inc {σ `→ τ  } T = λ inc′ → T $′ trans inc inc′

wk^βι : {Δ Γ : Con}{σ : ty} (inc : Γ ⊆ Δ) (T : Γ ⊨^βι σ) → Δ ⊨^βι σ
wk^βι inc (t , inj₁ ne)  = wk^⊢ inc t , inj₁ (wk^whne inc ne)
wk^βι inc (t , inj₂ T)   = wk^⊢ inc t , inj₂ (wk^βι⋆ inc T)

reflect^βι : {Γ : Con} (σ : ty) (t : Γ ⊢^whne σ) → Γ ⊨^βι σ
reflect^βι σ t = erase^whne t , inj₁ t
\end{code}

Reification is following the usual pattern; once more we avoid
η-expansion at all cost.

\begin{code}
mutual

  reify^βι⋆ : {Γ : Con} (σ : ty) (T : Γ ⊨^βι⋆ σ) → Γ ⊢^whnf σ
  reify^βι⋆ `Unit     T = `⟨⟩
  reify^βι⋆ `Bool     T = if T then `tt else `ff
  reify^βι⋆ (σ `→ τ)  T = `λ $ proj₁ $ T (step refl) var‿0^βι
    where var‿0^βι = reflect^βι _ $ `var here!

  reify^βι : {Γ : Con} (σ : ty) (T : Γ ⊨^βι σ) → Γ ⊢^whnf σ
  reify^βι σ (t , inj₁ ne) = `embed ne
  reify^βι σ (t , inj₂ T)  = reify^βι⋆ σ T
\end{code}

One important difference in the application rule with respect
to the previous subsection is that we do not grow the spine of
a stuck term using the reified argument but rather its \emph{source}
term thus staying true to the idea that we only head reduce
enough to expose either a constructor or a variable. The same
goes for \AF{ifte^{βι}}.

\begin{code}
infixr 5 _$^βι_
_$^βι_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βι σ `→ τ) (u : Γ ⊨^βι σ) → Γ ⊨^βι τ
(t , inj₁ ne)  $^βι (u , U) = t `$ u , inj₁ (ne `$ u)
(t , inj₂ T)   $^βι (u , U) = t `$ u , proj₂ (T refl (u , U))

ifte^βι : {Γ : Con} {σ : ty} (b : Γ ⊨^βι `Bool) (l r : Γ ⊨^βι σ) → Γ ⊨^βι σ
ifte^βι (b , inj₁ ne)  (l , L) (r , R) = `ifte b l r , inj₁ (`ifte ne l r)
ifte^βι (b , inj₂ B)   (l , L) (r , R) = `ifte b l r , (if B then L else R)


Normalise^βι : Semantics _⊨^βι_ _⊨^βι_
Normalise^βι =
  record  { embed   = λ σ → reflect^βι σ ∘ `var
          ; wk      = wk^βι
          ; ⟦var⟧   = id
          ; _⟦$⟧_   = _$^βι_
          ; ⟦λ⟧     = λ t → `λ (proj₁ $ t (step refl) (reflect^βι _ $ `var here!)) , inj₂ t
          ; ⟦⟨⟩⟧    = `⟨⟩ , inj₂ tt
          ; ⟦tt⟧    = `tt , inj₂ true
          ; ⟦ff⟧    = `ff , inj₂ false
          ; ⟦ifte⟧  = ifte^βι
          }

norm^βι : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^whnf σ
norm^βι σ t = reify^βι σ $′ Normalise^βι ⊨eval t
\end{code}

\section{Proving Properties of Semantics}
\label{properties}

Thanks to the introduction of \AF{Semantics}, we have already saved
quite a bit of work by not reimplementing the same traversals over
and over again. But this disciplined approach to building models and
defining the associated evaluation functions can also help us refactor
the process of proving some properties of these semantics.

Instead of using proof scripts as Benton et al.~\cite{benton2012strongly}
do, we describe abstractly the constraints the logical relations~\cite{reynolds1983types}
defined on model (and environment) values have to respect for us to be
able to conclude that the evaluation of a term in related environments
produces related outputs. This gives us a generic proof framework to
state and prove, in one go, properties about all of these semantics.

Our first example of such a framework will stay simple on purpose.
However this does not mean that it is a meaningless exercise: the
result proven here will actually be useful in the following subsections
when considering more complex properties.

\subsection{The Synchronisation Relation}

This first presentation should give the reader a good idea of the
internal organisation of this type of setup before we move on to a
more involved one. The types involved might look a bit scary because
of the level of generality that we adopt but the idea is rather simple:
two \AR{Semantics} are said to be \emph{synchronisable} if, when
evaluating a term in related environments, they output related values.
The bulk of the work is to make this intuition formal.

The evidence that two \AR{Semantics} are \AR{Synchronisable} is
packaged in a record. The record is indexed by the two semantics
as well as three relations. The first relation (\AB{Rel𝓔^{AB}})
characterises the elements of the (respective) environment types
which are to be considered synchronised, the second (\AB{Rel𝓔})
explains what it means for two environments to be synchronised
and the last (\AB{Rel𝓜}) describes what synchronisation means
in the model.

\begin{code}
record Synchronisable
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓜^A : (Γ : Con) (σ : ty) → Set ℓ^MA} (𝓢^A : Semantics 𝓔^A 𝓜^A)
  {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓜^B : (Γ : Con) (σ : ty) → Set ℓ^MB} (𝓢^B : Semantics 𝓔^B 𝓜^B)
  {ℓ^RE ℓ^RM ℓ^REAB : Level} (Rel𝓔^AB : {Γ : Con} {σ : ty} (eA : 𝓔^A Γ σ) (eB : 𝓔^B Γ σ) → Set ℓ^REAB)
  (Rel𝓔 : {Δ Γ : Con} (eA : Δ [ 𝓔^A ] Γ) (eB : Δ [ 𝓔^B ] Γ) → Set ℓ^RE)
  (Rel𝓜 : {Γ : Con} {σ : ty} (mA : 𝓜^A Γ σ) (mB : 𝓜^B Γ σ) → Set ℓ^RM)
  : Set (ℓ^RE ⊔ ℓ^RM ⊔ ℓ^EA ⊔ ℓ^EB ⊔ ℓ^MA ⊔ ℓ^MB ⊔ ℓ^REAB) where
\end{code}

The record's fields are describing the structure these relations
need to have. The first topic of interest is the interaction
between \AB{Rel𝓔^{AB}} and \AB{Rel𝓔}. \ARF{Rel𝓔∙} states that
it should be possible to extend two synchronised environments as
long the elements we push onto them are themselves related by
\AB{Rel𝓔^{AB}}. \ARF{Rel𝓔Wk} states that two synchronised
environments can be weakened whilst staying synchronised.

\AgdaHide{
\begin{code}
  module SemA = Semantics 𝓢^A
  module SemB = Semantics 𝓢^B
  field
\end{code}}
\begin{code}
    Rel𝓔∙   :  {Γ Δ : Con} {σ : ty} {ρA : Δ [ 𝓔^A ] Γ} {ρB : Δ [ 𝓔^B ] Γ} {uA : 𝓔^A Δ σ} {uB : 𝓔^B Δ σ} (ρR : Rel𝓔 ρA ρB) (uR : Rel𝓔^AB uA uB) →
                 Rel𝓔 ([ 𝓔^A ] ρA `∙ uA) ([ 𝓔^B ] ρB `∙ uB)
    Rel𝓔Wk  :  {Γ Δ Θ : Con} (inc : Δ ⊆ Θ) {ρA : Δ [ 𝓔^A ] Γ} {ρB : Δ [ 𝓔^B ] Γ} (ρR : Rel𝓔 ρA ρB) →
                 Rel𝓔  (wk[ SemA.wk ] inc ρA)
                         (wk[ SemB.wk ] inc ρB)
\end{code}

We then have the relational counterparts of the term constructors.
In order to lighten the presentation, we will mostly focus on the
interesting ones and give only one example quite characteristic of
the other ones.

The first interesting case is the relational counterpart of the
\AIC{`var} constructor: it states that given two synchronised
environments, we indeed get synchronised values in the model by
looking up the values each one of these associates to a given
variable.
\begin{code}
    R⟦var⟧    :  {Γ Δ : Con} {σ : ty} (v : σ ∈ Γ) {ρA : Δ [ 𝓔^A ] Γ} {ρB : Δ [ 𝓔^B ] Γ} (ρR : Rel𝓔 ρA ρB) →
                 Rel𝓜  (𝓢^A ⊨⟦ `var v ⟧ ρA)
                         (𝓢^B ⊨⟦ `var v ⟧ ρB)
\end{code}

The second, and probably most interesting case, is the description
of the relational counterpart of the \AIC{`λ}-abstraction which is
guided by the type of the \ARF{⟦λ⟧} combinator. It states that the
ability to evaluate the body of the λ in weakened environments each
extended by related values and deliver synchronised values in the
model is enough to guarantee that evaluating the lambdas in the original
environments will deliver synchronised values.

\begin{code}
    R⟦λ⟧      :  {Γ Δ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) {ρA : Δ [ 𝓔^A ] Γ} {ρB : Δ [ 𝓔^B ] Γ} (ρR : Rel𝓔 ρA ρB) →
                 (r :  {Θ : Con} (inc : Δ ⊆ Θ) {uA : 𝓔^A Θ σ} {uB : 𝓔^B Θ σ} (uR : Rel𝓔^AB uA uB) →
                       let ρA′  = [ 𝓔^A ] wk[ SemA.wk ] inc ρA `∙ uA
                           ρB′  = [ 𝓔^B ] wk[ SemB.wk ] inc ρB `∙ uB
                       in Rel𝓜  (𝓢^A ⊨⟦ t ⟧ ρA′) (𝓢^B ⊨⟦ t ⟧ ρB′)) →
                 Rel𝓜 (𝓢^A ⊨⟦ `λ t ⟧ ρA) (𝓢^B ⊨⟦ `λ t ⟧ ρB)
\end{code}

All the remaining cases are similar. We show here the relational
counterpart of the application constructor: it states that given
two induction hypotheses (and the knowledge that the two environment
used are synchronised), one can combine them to obtain a proof
about the evaluation of an application-headed term.

\begin{code}
    R⟦$⟧      :  {Γ Δ : Con} {σ τ : ty} (f : Γ ⊢ σ `→ τ) (t : Γ ⊢ σ) {ρA : Δ [ 𝓔^A ] Γ} {ρB : Δ [ 𝓔^B ] Γ} (ρR : Rel𝓔 ρA ρB) →
                 Rel𝓜 (𝓢^A ⊨⟦ f ⟧ ρA) (𝓢^B ⊨⟦ f ⟧ ρB) →
                 Rel𝓜 (𝓢^A ⊨⟦ t ⟧ ρA) (𝓢^B ⊨⟦ t ⟧ ρB) →
                 Rel𝓜 (𝓢^A ⊨⟦ f `$ t ⟧ ρA) (𝓢^B ⊨⟦ f `$ t ⟧ ρB)
\end{code}
\AgdaHide{
\begin{code}
    R⟦⟨⟩⟧     :  {Γ Δ : Con} {ρA : Δ [ 𝓔^A ] Γ} {ρB : Δ [ 𝓔^B ] Γ} (ρR : Rel𝓔 ρA ρB) →
                 Rel𝓜 (𝓢^A ⊨⟦ `⟨⟩ ⟧ ρA) (𝓢^B ⊨⟦ `⟨⟩ ⟧ ρB)
    R⟦tt⟧     :  {Γ Δ : Con} {ρA : Δ [ 𝓔^A ] Γ} {ρB : Δ [ 𝓔^B ] Γ} (ρR : Rel𝓔 ρA ρB) →
                 Rel𝓜 (𝓢^A ⊨⟦ `tt ⟧ ρA) (𝓢^B ⊨⟦ `tt ⟧ ρB)
    R⟦ff⟧     :  {Γ Δ : Con} {ρA : Δ [ 𝓔^A ] Γ} {ρB : Δ [ 𝓔^B ] Γ} (ρR : Rel𝓔 ρA ρB) →
                 Rel𝓜 (𝓢^A ⊨⟦ `ff ⟧ ρA) (𝓢^B ⊨⟦ `ff ⟧ ρB)
    R⟦ifte⟧   :  {Γ Δ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ) {ρA : Δ [ 𝓔^A ] Γ} {ρB : Δ [ 𝓔^B ] Γ} (ρR : Rel𝓔 ρA ρB) →
                 Rel𝓜 (𝓢^A ⊨⟦ b ⟧ ρA) (𝓢^B ⊨⟦ b ⟧ ρB) →
                 Rel𝓜 (𝓢^A ⊨⟦ l ⟧ ρA) (𝓢^B ⊨⟦ l ⟧ ρB) →
                 Rel𝓜 (𝓢^A ⊨⟦ r ⟧ ρA) (𝓢^B ⊨⟦ r ⟧ ρB) →
                 Rel𝓜 (𝓢^A ⊨⟦ `ifte b l r ⟧ ρA) (𝓢^B ⊨⟦ `ifte b l r ⟧ ρB)
\end{code}}

For this specification to be useful, we need to verify that it is indeed
possible for us to benefit from its introduction which we can conclude
based on two observations. First, our ability to prove a fundamental lemma
stating that given relations satisfying this specification, the evaluation
of a term in related environments yields related values; second, our ability
to find with various instances of such synchronised semantics. Let us start
with the fundamental lemma.

\subsubsection{Fundamental Lemma of Synchronisable Semantics}

The fundamental lemma is indeed provable. We introduce a \AM{Synchronised}
module parametrised by a record packing the evidence that two semantics are
\AR{Synchronisable}. This allows us to bring all of the corresponding relational
counterpart of term constructors into scope by \AK{open}ing the record. The
traversal then uses them to combine the induction hypotheses arising structurally.

\begin{code}
module Synchronised {ℓ^EA ℓ^MA ℓ^EB ℓ^MB : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓜^A : (Γ : Con) (σ : ty) → Set ℓ^MA} {𝓢^A : Semantics 𝓔^A 𝓜^A} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓜^B : (Γ : Con) (σ : ty) → Set ℓ^MB} {𝓢^B : Semantics 𝓔^B 𝓜^B} {ℓ^RE ℓ^RM ℓ^REAB : Level} {Rel𝓔^AB : {Γ : Con} {σ : ty} (eA : 𝓔^A Γ σ) (eB : 𝓔^B Γ σ) → Set ℓ^REAB} {Rel𝓔 : {Δ Γ : Con} (eA : Δ [ 𝓔^A ] Γ) (eB : Δ [ 𝓔^B ] Γ) → Set ℓ^RE} {Rel𝓜 : {Γ : Con} {σ : ty} (mA : 𝓜^A Γ σ) (mB : 𝓜^B Γ σ) → Set ℓ^RM} (rel : Synchronisable 𝓢^A 𝓢^B Rel𝓔^AB Rel𝓔 Rel𝓜) where
  open Synchronisable rel

  lemma : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) {ρA : Δ [ 𝓔^A ] Γ} {ρB : Δ [ 𝓔^B ] Γ} (ρ^R : Rel𝓔 ρA ρB) → Rel𝓜 (𝓢^A ⊨⟦ t ⟧ ρA) (𝓢^B ⊨⟦ t ⟧ ρB)
  lemma (`var v)       ρ^R = R⟦var⟧ v ρ^R
  lemma (f `$ t)       ρ^R = R⟦$⟧ f t ρ^R (lemma f ρ^R) (lemma t ρ^R)
  lemma (`λ t)         ρ^R = R⟦λ⟧ t ρ^R $ λ inc u^R → lemma t (Rel𝓔∙ (Rel𝓔Wk inc ρ^R) u^R)
  lemma `⟨⟩            ρ^R = R⟦⟨⟩⟧ ρ^R
  lemma `tt            ρ^R = R⟦tt⟧ ρ^R
  lemma `ff            ρ^R = R⟦ff⟧ ρ^R
  lemma (`ifte b l r)  ρ^R = R⟦ifte⟧ b l r ρ^R (lemma b ρ^R) (lemma l ρ^R) (lemma r ρ^R)
\end{code}

\subsubsection{Examples of Synchronisable Semantics}

Our first example of two synchronisable semantics is proving the
fact that \AF{Renaming} and \AF{Substitution} have precisely the
same behaviour whenever the environment we use for \AF{Substitution}
is only made up of variables. The (mundane) proofs which mostly
consist of using the congruence of propositional equality are
left out. We show with the lemma \AF{RenamingIsASubstitution} how
the result is derived directly from the fundamental lemma of
\AR{Synchronisable} semantics.

\begin{code}
SynchronisableRenamingSubstitution : Synchronisable Renaming Substitution
  (λ v t → `var v ≡ t)
  (λ ρA ρB → (σ : ty) (pr : σ ∈ _) → `var (ρA σ pr) ≡ ρB σ pr)
  _≡_
\end{code}
\AgdaHide{
\begin{code}
SynchronisableRenamingSubstitution =
  record
    { Rel𝓔∙   = λ ρR uR → [ uR , ρR ]
    ; Rel𝓔Wk  = λ inc ρR σ pr → PEq.cong (wk^⊢ inc) (ρR σ pr)
    ; R⟦var⟧    = λ v ρR → ρR _ v
    ; R⟦$⟧      = λ _ _ _ → PEq.cong₂ _`$_
    ; R⟦λ⟧      = λ _  ρR r → PEq.cong `λ (r (step refl) PEq.refl)
    ; R⟦⟨⟩⟧     = λ _  → PEq.refl
    ; R⟦tt⟧     = λ _  → PEq.refl
    ; R⟦ff⟧     = λ _  → PEq.refl
    ; R⟦ifte⟧   = λ _ _ _ _ eqb eql → PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ eqb eql)
    }
\end{code}}\vspace{-1.5em}%ugly but it works!
\begin{code}
RenamingIsASubstitution :  {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ flip (_∈_) ] Γ) →
                           Renaming ⊨⟦ t ⟧ ρ ≡ Substitution ⊨⟦ t ⟧ (λ σ → `var ∘ ρ σ)
RenamingIsASubstitution t ρ = RenSubst.lemma t (λ σ pr → PEq.refl)
  where module RenSubst = Synchronised SynchronisableRenamingSubstitution
\end{code}


Another example of synchronisable semantics is normalisation by evaluation
which can be synchronised with itself. This may appear like mindless symbol
pushing but it is actually crucial to prove such a theorem: we can only
define a Partial Equivalence Relation~\cite{mitchell1996foundations} (PER)
on the model and the properties of the Normalisation by Evaluation procedure
will rely heavily on the fact that the exotic elements that may exist in the
host language are actually never produced by the evaluation function as long
as all the elements of the environment were, themselves, not exotic (i.e. one
part of the PER's diagonal).

We start with the definition of the PER for the model. It is defined by
induction on the type and ensures that terms which behave the same
extensionally are declared equal.

\begin{code}
EQREL : (Γ : Con) (σ : ty) (T U : Γ ⊨^βιξη σ) → Set
EQREL Γ `Unit     T U = ⊤
EQREL Γ `Bool     T U = T ≡ U
EQREL Γ (σ `→ τ)  T U =
  {Δ : Con} (inc : Γ ⊆ Δ) {V W : Δ ⊨^βιξη σ} (eqVW : EQREL Δ σ V W) →
  EQREL Δ τ (T inc V) (U inc W)
\end{code}

It is indeed a PER as witnessed by \AF{symEQREL} and \AF{transEQREL}
(not shown here) and it respects weakening (\AF{wk^{EQREL}}).

\AgdaHide{
\begin{code}
wk^EQREL : {Δ Γ : Con} (σ : ty) (inc : Γ ⊆ Δ) {T U : Γ ⊨^βιξη σ} →
           EQREL Γ σ T U → EQREL Δ σ (wk^βιξη σ inc T) (wk^βιξη σ inc U)
wk^EQREL `Unit     inc eq = tt
wk^EQREL `Bool     inc eq = PEq.cong (wk^nf inc) eq
wk^EQREL (σ `→ τ)  inc eq = λ inc′ eqVW → eq (trans inc inc′) eqVW

symEQREL : {Γ : Con} (σ : ty) {S T : Γ ⊨^βιξη σ} →
           EQREL Γ σ S T → EQREL Γ σ T S
symEQREL `Unit     eq = tt
symEQREL `Bool     eq = PEq.sym eq
symEQREL (σ `→ τ)  eq = λ inc eqVW → symEQREL τ (eq inc (symEQREL σ eqVW))

mutual

  transEQREL : {Γ : Con} (σ : ty) {S T U : Γ ⊨^βιξη σ} →
               EQREL Γ σ S T → EQREL Γ σ T U → EQREL Γ σ S U
  transEQREL `Unit     eq₁ eq₂ = tt
  transEQREL `Bool     eq₁ eq₂ = PEq.trans eq₁ eq₂
  transEQREL (σ `→ τ)  eq₁ eq₂ =
    λ inc eqVW → transEQREL τ (eq₁ inc (reflEQREL σ eqVW)) (eq₂ inc eqVW)

  -- We are in PER so reflEQREL is not provable
  -- but as soon as EQREL σ V W then EQREL σ V V
  reflEQREL : {Γ : Con} (σ : ty) {S T : Γ ⊨^βιξη σ} →
              EQREL Γ σ S T → EQREL Γ σ S S
  reflEQREL σ eq = transEQREL σ eq (symEQREL σ eq)
\end{code}}

The interplay of reflect and reify with this notion of equality have
to be described in one go because of their being mutually defined.

\begin{code}
reify^EQREL    :  {Γ : Con} (σ : ty) {T U : Γ ⊨^βιξη σ} (EQTU : EQREL Γ σ T U) →
                  reify^βιξη σ T ≡ reify^βιξη σ U
reflect^EQREL  :  {Γ : Con} (σ : ty) {t u : Γ ⊢^ne σ} (eq : t ≡ u) →
                  EQREL Γ σ (reflect^βιξη σ t) (reflect^βιξη σ u)
\end{code}
\AgdaHide{
\begin{code}
reify^EQREL `Unit     EQTU = PEq.refl
reify^EQREL `Bool     EQTU = EQTU
reify^EQREL (σ `→ τ)  EQTU = PEq.cong `λ $ reify^EQREL τ $ EQTU (step refl) $ reflect^EQREL σ PEq.refl

reflect^EQREL `Unit     eq = tt
reflect^EQREL `Bool     eq = PEq.cong `embed eq
reflect^EQREL (σ `→ τ)  eq = λ inc rel → reflect^EQREL τ $ PEq.cong₂ _`$_ (PEq.cong (wk^ne inc) eq) (reify^EQREL σ rel)

ifteRelNorm :
      {Γ Δ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
      {ρA ρB : Δ [ _⊨^βιξη_ ] Γ} →
      ((σ₁ : ty) (pr : σ₁ ∈ Γ) → EQREL Δ σ₁ (ρA σ₁ pr) (ρB σ₁ pr)) →
      Normalise^βιξη ⊨⟦ b ⟧ ρA ≡ Normalise^βιξη ⊨⟦ b ⟧ ρB →
      EQREL Δ σ (Normalise^βιξη ⊨⟦ l ⟧ ρA) (Normalise^βιξη ⊨⟦ l ⟧ ρB) →
      EQREL Δ σ (Normalise^βιξη ⊨⟦ r ⟧ ρA) (Normalise^βιξη ⊨⟦ r ⟧ ρB) →
      EQREL Δ σ (Normalise^βιξη ⊨⟦ `ifte b l r ⟧ ρA)
      (Normalise^βιξη ⊨⟦ `ifte b l r ⟧ ρB)
ifteRelNorm b l r {ρA} {ρB} ρR eqb eql eqr
  with Normalise^βιξη ⊨⟦ b ⟧ ρA
     | Normalise^βιξη ⊨⟦ b ⟧ ρB
ifteRelNorm b l r ρR PEq.refl eql eqr | `embed t | `embed .t =
  reflect^EQREL _ (PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ PEq.refl (reify^EQREL _ eql)) (reify^EQREL _ eqr))
ifteRelNorm b l r ρR () eql eqr | `embed t | `tt
ifteRelNorm b l r ρR () eql eqr | `embed t | `ff
ifteRelNorm b l r ρR () eql eqr | `tt | `embed t
ifteRelNorm b l r ρR PEq.refl eql eqr | `tt | `tt = eql
ifteRelNorm b l r ρR () eql eqr | `tt | `ff
ifteRelNorm b l r ρR () eql eqr | `ff | `embed t
ifteRelNorm b l r ρR () eql eqr | `ff | `tt
ifteRelNorm b l r ρR PEq.refl eql eqr | `ff | `ff = eqr
\end{code}}

And that's enough to prove that evaluating a term in two
environments related in a pointwise manner by \AF{EQREL}
yields two semantic objects themselves related by \AF{EQREL}:

\begin{code}
SynchronisableNormalise :
  Synchronisable Normalise^βιξη Normalise^βιξη
    (EQREL _ _)
    (λ ρA ρB → (σ : ty) (pr : σ ∈ _) → EQREL _ σ (ρA σ pr) (ρB σ pr))
    (EQREL _ _)
\end{code}
\AgdaHide{
\begin{code}
SynchronisableNormalise =
  record
    { Rel𝓔∙  = λ ρR uR → [ uR , ρR ]
    ; Rel𝓔Wk = λ inc ρR σ pr → wk^EQREL σ inc (ρR σ pr)
    ; R⟦var⟧   = λ v ρR → ρR _ v
    ; R⟦$⟧     = λ _ _ _ f → f refl
    ; R⟦λ⟧     = λ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ → tt
    ; R⟦tt⟧    = λ _ → PEq.refl
    ; R⟦ff⟧    = λ _ → PEq.refl
    ; R⟦ifte⟧  = ifteRelNorm
    }
\end{code}}

We can now move on to the more complex example of a proof
framework built generically over our notion of \AF{Semantics}

\subsection{Fusions of Evaluations}

One thing that one needs to systematically prove in order to be
able to start working on the meta-theory of a calculus is that
various semantics can be fused. If we just consider the two
syntactic semantics we introduced earlier, that leads to four
lemmas already. That led us to defining a fusion framework
describing how to relate three semantics.

The evidence that \AB{𝓢^A}, \AB{𝓢^B} and \AB{𝓢^C} are such
that \AB{𝓢^A} followed by \AB{𝓢^B} can be said to be equivalent
to \AB{𝓢^C} (e.g. think \AF{Substitution} followed by \AF{Renaming}
can be reduced to \AF{Substitution}) is packed in a record
\AR{Fusable} indexed by the three semantics but also three
relations. The first one (\AB{Rel𝓔^BC}) states what it means
for two environment values of \AB{𝓢^B} and \AB{𝓢^C} respectively
to be related. The second one (\AB{Rel𝓔}) characteries the triples
of environments (one for each one of the semantics) which are
compatible. Finally, the last one (\AB{Rel𝓜}) relates values
in \AB{𝓢^B} and \AB{𝓢^C}'s respective models.

\begin{code}
record Fusable
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REBC ℓ^RM : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓔^C : (Γ : Con) (σ : ty) → Set ℓ^EC} {𝓜^A : (Γ : Con) (σ : ty) → Set ℓ^MA} {𝓜^B : (Γ : Con) (σ : ty) → Set ℓ^MB} {𝓜^C : (Γ : Con) (σ : ty) → Set ℓ^MC} (𝓢^A      : Semantics 𝓔^A 𝓜^A)
  (𝓢^B      : Semantics 𝓔^B 𝓜^B)
  (𝓢^C      : Semantics 𝓔^C 𝓜^C)
  (Rel𝓔^BC  : {Γ : Con} {σ : ty} (eB : 𝓔^B Γ σ) (eC : 𝓔^C Γ σ) → Set ℓ^REBC)
  (Rel𝓔    :  {Θ Δ Γ : Con} (eA : Δ [ 𝓔^A ] Γ) (ρB : Θ [ 𝓔^B ] Δ)
                (eC : Θ [ 𝓔^C ] Γ) → Set ℓ^RE)
  (Rel𝓜    : {Γ : Con} {σ : ty} (mB : 𝓜^B Γ σ) (mC : 𝓜^C Γ σ) → Set ℓ^RM)
  : Set (ℓ^RM ⊔ ℓ^RE ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA ⊔ ℓ^MA ⊔ ℓ^REBC) where
\end{code}
\AgdaHide{
\begin{code}
  module SemA = Semantics 𝓢^A
  module SemB = Semantics 𝓢^B
  module SemC = Semantics 𝓢^C
  field
\end{code}}

Similarly to the previous section, most of the fields of this
record describe what structure these relations need to have.
However, we start with something slightly different: given that
we are planing to run the \AR{Semantics} \AB{𝓢^B} \emph{after}
having run \AB{𝓢^A}, we need a way to extract a term from an
element of \AB{𝓢^A}'s model. Our first field is therefore
\ARF{reifyA}:

\begin{code}
    reifyA    : {Γ : Con} {σ : ty} (m : 𝓜^A Γ σ) → Γ ⊢ σ
\end{code}

Then come two constraints dealing with the relations talking
about evaluation environments. \ARF{Rel𝓔∙} tells us how to
extend related environments: one should be able to push related
values onto the environments for \AB{𝓢^B} and \AB{𝓢^C} whilst
merely extending the one for \AB{𝓢^A} with a token value generated
using \ARF{embed}.

\ARF{Rel𝓔Wk} guarantees that it is always possible to weaken
the environments for \AB{𝓢^B} and \AB{𝓢^C} in a \AB{Rel𝓔}
preserving manner.

\begin{code}
    Rel𝓔∙   :  {Γ Δ Θ : Con} {σ : ty} {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ} {uB : 𝓔^B Θ σ} {uC : 𝓔^C Θ σ} (ρR : Rel𝓔 ρA ρB ρC) (uR : Rel𝓔^BC uB uC) →
                 Rel𝓔  ([ 𝓔^A ]  wk[ SemA.wk ] (step refl) ρA
                                    `∙ SemA.embed σ here!)
                         ([ 𝓔^B ]  ρB `∙ uB)
                         ([ 𝓔^C ]  ρC `∙ uC)

    Rel𝓔Wk  :  {Γ Δ Θ E : Con} (inc : Θ ⊆ E) {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ} (ρR : Rel𝓔 ρA ρB ρC) →
                 Rel𝓔 ρA  (wk[ SemB.wk ] inc ρB)
                            (wk[ SemC.wk ] inc ρC)
\end{code}

Then we have the relational counterpart of the various term
constructors. As with the previous section, only a handful of
them are out of the ordinary. We will start with the \AIC{`var}
case. It states that fusion indeed happens when evaluating a
variable using related environments.

\begin{code}
    R⟦var⟧  : {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ} (ρR : Rel𝓔 ρA ρB ρC) →
              Rel𝓜  (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ `var v ⟧ ρA) ⟧ ρB)
                      (𝓢^C ⊨⟦ `var v ⟧ ρC)
\end{code}

The \AIC{`λ}-case puts some rather strong restrictions on the way
the λ-abstraction's body may be used by \AB{𝓢^A}: we assume it
is evaluated in an environment weakened by one variable and extended
using \AB{𝓢^A}'s \ARF{embed}. But it is quite natural to have these
restrictions: given that \ARF{reifyA} quotes the result back, we are
expecting this type of evaluation in an extended context (i.e. under
one lambda). And it turns out that this is indeed enough for all of
our examples.

The evaluation environments used by the semantics \AB{𝓢^B} and \AB{𝓢^C}
on the other can be arbitrarily weakened before being extended with related
values to be substituted for the variable bound by the \AIC{`λ}.

\begin{code}
    R⟦λ⟧    :  {Γ Δ Θ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ} (ρR : Rel𝓔 ρA ρB ρC) →
               (r :  {E : Con} (inc : Θ ⊆ E) {uB : 𝓔^B E σ} {uC : 𝓔^C E σ} (uR : Rel𝓔^BC uB uC) →
                     let  ρA′ =  [ 𝓔^A ] wk[ SemA.wk ] (step refl) ρA
                                 `∙ SemA.embed σ here!
                          ρB′ =  [ 𝓔^B ] wk[ SemB.wk ] inc ρB `∙ uB
                          ρC′ =  [ 𝓔^C ] wk[ SemC.wk ] inc ρC `∙ uC
                     in Rel𝓜  (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ t ⟧ ρA′) ⟧ ρB′)
                                (𝓢^C ⊨⟦ t ⟧ ρC′)) →
                Rel𝓜  (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ `λ t ⟧ ρA) ⟧ ρB)
                        (𝓢^C ⊨⟦ `λ t ⟧ ρC)
\end{code}

The other cases are just a matter of stating that, given the
expected induction hypotheses, one can deliver a proof that
fusion can happen on the compound expression.

\AgdaHide{
\begin{code}
    R⟦$⟧    : {Γ Δ Θ : Con} {σ τ : ty} (f : Γ ⊢ σ `→ τ) (t : Γ ⊢ σ)
            {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ} →
             (ρR : Rel𝓔 ρA ρB ρC) →
            Rel𝓜 (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ f ⟧ ρA) ⟧ ρB)
                   (𝓢^C ⊨⟦ f ⟧ ρC) →
            Rel𝓜 (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ t ⟧ ρA) ⟧ ρB) (𝓢^C ⊨⟦ t ⟧ ρC) →
            Rel𝓜 (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ f `$ t ⟧ ρA) ⟧ ρB) (𝓢^C ⊨⟦ f `$ t ⟧ ρC)

    R⟦⟨⟩⟧   : {Γ Δ Θ : Con} {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ} →
             (ρR : Rel𝓔 ρA ρB ρC) →
            Rel𝓜 (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ `⟨⟩ ⟧ ρA) ⟧ ρB) (𝓢^C ⊨⟦ `⟨⟩ ⟧ ρC)
    R⟦tt⟧   : {Γ Δ Θ : Con} {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ} →
             (ρR : Rel𝓔 ρA ρB ρC) →
            Rel𝓜 (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ `tt ⟧ ρA) ⟧ ρB) (𝓢^C ⊨⟦ `tt ⟧ ρC)
    R⟦ff⟧   : {Γ Δ Θ : Con} {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ} →
             (ρR : Rel𝓔 ρA ρB ρC) →
            Rel𝓜 (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ `ff ⟧ ρA) ⟧ ρB) (𝓢^C ⊨⟦ `ff ⟧ ρC)
    R⟦ifte⟧ : {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
            {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ} →
             (ρR : Rel𝓔 ρA ρB ρC) →
            Rel𝓜 (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ b ⟧ ρA) ⟧ ρB) (𝓢^C ⊨⟦ b ⟧ ρC) →
            Rel𝓜 (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ l ⟧ ρA) ⟧ ρB) (𝓢^C ⊨⟦ l ⟧ ρC) →
            Rel𝓜 (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ r ⟧ ρA) ⟧ ρB) (𝓢^C ⊨⟦ r ⟧ ρC) →
            Rel𝓜 (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ `ifte b l r ⟧ ρA) ⟧ ρB) (𝓢^C ⊨⟦ `ifte b l r ⟧ ρC)
\end{code}}

\subsubsection{Fundamental Lemma of Fusable Semantics}

As with synchronisation, we measure the usefulness of this framework
by the fact that we can prove its fundamental lemma first and that
we get useful theorems out of it second. Once again, having carefully
identified what the constraints should be, proving the fundamental
lemma turns out to amount to a simple traversal we choose to omit here.

\begin{code}
module Fusion
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REB ℓ^RM : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓔^C : (Γ : Con) (σ : ty) → Set ℓ^EC} {𝓜^A : (Γ : Con) (σ : ty) → Set ℓ^MA} {𝓜^B : (Γ : Con) (σ : ty) → Set ℓ^MB} {𝓜^C : (Γ : Con) (σ : ty) → Set ℓ^MC} {𝓢^A : Semantics 𝓔^A 𝓜^A} {𝓢^B : Semantics 𝓔^B 𝓜^B} {𝓢^C : Semantics 𝓔^C 𝓜^C} {Rel𝓔^BC : {Γ : Con} {σ : ty} (eB : 𝓔^B Γ σ) (eC : 𝓔^C Γ σ) → Set ℓ^REB} {Rel𝓔 : {Θ Δ Γ : Con} (ρA : Δ [ 𝓔^A ] Γ) (ρB : Θ [ 𝓔^B ] Δ) (ρC : Θ [ 𝓔^C ] Γ) → Set ℓ^RE} {Rel𝓜 : {Γ : Con} {σ : ty} (mB : 𝓜^B Γ σ) (mC : 𝓜^C Γ σ) → Set ℓ^RM} (fusable : Fusable 𝓢^A 𝓢^B 𝓢^C Rel𝓔^BC Rel𝓔 Rel𝓜)
  where
  open Fusable fusable

  fusion :  {Γ Δ Θ : Con} {σ : ty} (t : Γ ⊢ σ) {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ} (ρR : Rel𝓔 ρA ρB ρC) →
            Rel𝓜  (𝓢^B ⊨⟦ reifyA (𝓢^A ⊨⟦ t ⟧ ρA) ⟧ ρB)
                    (𝓢^C ⊨⟦ t ⟧ ρC)
\end{code}
\AgdaHide{
\begin{code}
  fusion (`var v)       ρR = R⟦var⟧ v ρR
  fusion (f `$ t)       ρR = R⟦$⟧ f t ρR (fusion f ρR) (fusion t ρR)
  fusion (`λ t)         ρR = R⟦λ⟧ t ρR $ λ inc uR → fusion t (Rel𝓔∙ (Rel𝓔Wk inc ρR) uR)
  fusion `⟨⟩            ρR = R⟦⟨⟩⟧ ρR
  fusion `tt            ρR = R⟦tt⟧ ρR
  fusion `ff            ρR = R⟦ff⟧ ρR
  fusion (`ifte b l r)  ρR = R⟦ifte⟧ b l r ρR ihb ihl ihr
    where ihb = fusion b ρR
          ihl = fusion l ρR
          ihr = fusion r ρR
\end{code}}

\subsubsection{The Special Case of Syntactic Semantics}

Given that \AR{Syntactic} semantics use a lot of constructors
as their own semantic counterpart, it is possible to generate
evidence of them being fusable with much fewer assumptions.
We isolate them and prove the result generically in order to
avoid repeting ourselves.

A \AR{SyntacticFusable} record packs the evidence necessary to
prove that the \AR{Syntactic} semantics \AB{synA} and \AB{synB}
can be fused using the \AR{Syntactic} semantics \AB{synC}. It
is indexed by these three \AR{Syntactic}s as well as two relations
corresponding to the \AB{Rel𝓔^BC} and \AB{Rel𝓔} ones of the
\AR{Fusable} framework.

It contains the same \ARF{Rel𝓔∙}, \ARF{Rel𝓔Wk} and \ARF{R⟦var⟧}
fields as a \AR{Fusable} as well as a fourth one (\ARF{embedBC})
saying that \AB{synB} and \AB{synC}'s respective \ARF{embed}s are
producing related values.

\AgdaHide{
\begin{code}
record SyntacticFusable
  {ℓ^EA ℓ^EB ℓ^EC ℓ^REBC ℓ^RE : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓔^C : (Γ : Con) (σ : ty) → Set ℓ^EC} (synA : Syntactic 𝓔^A)
  (synB : Syntactic 𝓔^B)
  (synC : Syntactic 𝓔^C)
  (Rel𝓔^BC : {Γ : Con} {σ : ty} (eB : 𝓔^B Γ σ) (eC : 𝓔^C Γ σ) → Set ℓ^REBC)
  (Rel𝓔 : {Θ Δ Γ : Con} (ρA : Δ [ 𝓔^A ] Γ) (ρB : Θ [ 𝓔^B ] Δ) (ρC : Θ [ 𝓔^C ] Γ) → Set ℓ^RE)
  : Set (ℓ^RE ⊔ ℓ^REBC ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA)
  where
  module SynA = Syntactic synA
  module SynB = Syntactic synB
  module SynC = Syntactic synC
  field
    Rel𝓔∙ : ({Γ Δ Θ : Con} {σ : ty} {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ}
               {uB : 𝓔^B Θ σ} {uC : 𝓔^C Θ σ} (ρR : Rel𝓔 ρA ρB ρC) (uR : Rel𝓔^BC uB uC) →
               Rel𝓔 ([ 𝓔^A ] wk[ SynA.wk ] (step refl) ρA `∙ SynA.embed σ here!)
                      ([ 𝓔^B ] ρB `∙ uB)
                      ([ 𝓔^C ] ρC `∙ uC))
    Rel𝓔Wk : {Γ Δ Θ E : Con} (inc : Θ ⊆ E)
               {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ} (ρR : Rel𝓔 ρA ρB ρC) →
               Rel𝓔 ρA (wk[ SynB.wk ] inc ρB) (wk[ SynC.wk ] inc ρC)
    R⟦var⟧  : {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) {ρA : Δ [ 𝓔^A ] Γ} {ρB : Θ [ 𝓔^B ] Δ} {ρC : Θ [ 𝓔^C ] Γ}
              (ρR : Rel𝓔 ρA ρB ρC) →
              syntactic synB ⊨⟦ syntactic synA ⊨⟦ `var v ⟧ ρA ⟧ ρB ≡ syntactic synC ⊨⟦ `var v ⟧ ρC
\end{code}}
\begin{code}
    embedBC : {Γ : Con} {σ : ty} → Rel𝓔^BC  {Γ ∙ σ} (SynB.embed σ here!)
                                             (SynC.embed σ here!)
\end{code}

The important result is that given a \AR{SyntacticFusable} relating
three \AR{Syntactic} semantics, one can deliver a \AR{Fusable} relating
the corresponding \AR{Semantics} where \AB{Rel𝓜} is the propositional
equality.

\begin{code}
syntacticFusable :
  {ℓ^EA ℓ^EB ℓ^EC ℓ^RE ℓ^REBC : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓔^C : (Γ : Con) (σ : ty) → Set ℓ^EC} {synA : Syntactic 𝓔^A} {synB : Syntactic 𝓔^B} {synC : Syntactic 𝓔^C} {Rel𝓔^BC : {Γ : Con} {σ : ty} (eB : 𝓔^B Γ σ) (eC : 𝓔^C Γ σ) → Set ℓ^REBC} {Rel𝓔 : {Θ Δ Γ : Con} (ρA : Δ [ 𝓔^A ] Γ) (ρB : Θ [ 𝓔^B ] Δ) (ρC : Θ [ 𝓔^C ] Γ) → Set ℓ^RE} (synF : SyntacticFusable synA synB synC Rel𝓔^BC Rel𝓔) →
  Fusable  (syntactic synA) (syntactic synB) (syntactic synC)
           Rel𝓔^BC Rel𝓔 _≡_
\end{code}
\AgdaHide{
\begin{code}
syntacticFusable synF =
  let open SyntacticFusable synF in
  record
    { reifyA    = id
    ; Rel𝓔∙   = Rel𝓔∙
    ; Rel𝓔Wk  = Rel𝓔Wk
    ; R⟦var⟧    = R⟦var⟧
    ; R⟦$⟧      = λ f t ρR → PEq.cong₂ _`$_
    ; R⟦λ⟧      = λ t ρR r → PEq.cong `λ (r (step refl) embedBC)
    ; R⟦⟨⟩⟧     = λ ρR → PEq.refl
    ; R⟦tt⟧     = λ ρR → PEq.refl
    ; R⟦ff⟧     = λ ρR → PEq.refl
    ; R⟦ifte⟧   = λ b l r ρR eqb eql → PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ eqb eql)
    }

`var-inj : {Γ : Con} {σ : ty} {pr₁ pr₂ : σ ∈ Γ} (eq : (Γ ⊢ σ ∋ `var pr₁) ≡ `var pr₂) → pr₁ ≡ pr₂
`var-inj PEq.refl = PEq.refl
\end{code}}

It is then trivial to prove that \AR{Renaming} can be fused with itself
to give rise to another renaming (obtained by composing the two context
inclusions):

\begin{code}
RenamingFusable :
  SyntacticFusable  syntacticRenaming
                    syntacticRenaming
                    syntacticRenaming
                    _≡_
                    (λ ρA ρB ρC → ∀ σ pr → ρB σ (ρA σ pr) ≡ ρC σ pr)
\end{code}
\AgdaHide{
\begin{code}
RenamingFusable =
  record { Rel𝓔∙   = λ ρR eq → [ eq , ρR ]
         ; Rel𝓔Wk  = λ inc ρR σ pr → PEq.cong (inc σ) (ρR σ pr)
         ; R⟦var⟧    = λ v ρR → PEq.cong `var (ρR _ v)
         ; embedBC   = PEq.refl }
\end{code}}

Or that a \AR{Substitution} following a \AR{Renaming} is equivalent
to a \AR{Substitution} where the evaluation environment is the composition
of the two previous one.

\begin{code}
RenamingSubstitutionFusable :
  SyntacticFusable  syntacticRenaming
                    syntacticSubstitution
                    syntacticSubstitution
                    _≡_
                    (λ ρA ρB ρC → ∀ σ pr →
                       ρB σ (ρA σ pr) ≡ ρC σ pr)
\end{code}
\AgdaHide{
\begin{code}
RenamingSubstitutionFusable =
  record { Rel𝓔∙   = λ ρR eq → [ eq , ρR ]
         ; Rel𝓔Wk  = λ inc ρR σ pr → PEq.cong (Renaming ⊨⟦_⟧ inc) (ρR σ pr)
         ; R⟦var⟧    = λ v ρR → ρR _ v
         ; embedBC   = PEq.refl }
\end{code}}

Using the newly established fact about fusing two \AR{Renamings} together,
we can establish that a \AR{Substitution} followed by a \AR{Renaming} is
equivalent to a \AR{Substitution} where the elements in the evaluation
environment have been renamed.

\begin{code}
SubstitutionRenamingFusable :
  SyntacticFusable  syntacticSubstitution
                    syntacticRenaming
                    syntacticSubstitution
                    (λ v t → `var v ≡ t)
                    (λ ρA ρB ρC → ∀ σ pr →
                       Renaming ⊨⟦ ρA σ pr ⟧ ρB ≡ ρC σ pr)
\end{code}
\AgdaHide{
\begin{code}
SubstitutionRenamingFusable =
  let module RenRen = Fusion (syntacticFusable RenamingFusable) in
  record { Rel𝓔∙   = λ {_} {_} {_} {_} {ρA} {ρB} {ρC} ρR eq → [ eq , (λ σ pr →
                         PEq.trans (RenRen.fusion (ρA σ pr) (λ _ _ → PEq.refl))
                                   (ρR σ pr)) ]
         ; Rel𝓔Wk  = λ inc {ρA} {ρB} {ρC} ρR σ pr →
                         PEq.trans (PEq.sym (RenRen.fusion (ρA σ pr) (λ _ _ → PEq.refl)))
                                   (PEq.cong (Renaming ⊨⟦_⟧ inc) (ρR σ pr))
         ; R⟦var⟧    = λ v ρR → ρR _ v
         ; embedBC   = PEq.refl }
\end{code}}

Finally, using the fact that we now know how to fuse a \AR{Substitution}
and a \AR{Renaming} together no matter in which order they're performed,
we can prove that \AR{Substitution} can be fused with itself.

\begin{code}
SubstitutionFusable :
  SyntacticFusable  syntacticSubstitution
                    syntacticSubstitution
                    syntacticSubstitution
                    _≡_
                    (λ ρA ρB ρC → ∀ σ pr →
                       Substitution ⊨⟦ ρA σ pr ⟧ ρB ≡ ρC σ pr)
\end{code}
\AgdaHide{
\begin{code}
SubstitutionFusable =
  let module RenSubst = Fusion (syntacticFusable RenamingSubstitutionFusable)
      module SubstRen = Fusion (syntacticFusable SubstitutionRenamingFusable) in
  record { Rel𝓔∙   = λ {_} {_} {_} {_} {ρA} {ρB} {ρC} ρR eq → [ eq , (λ σ pr →
                         PEq.trans (RenSubst.fusion (ρA σ pr) (λ _ _ → PEq.refl))
                                   (ρR σ pr)) ]
         ; Rel𝓔Wk  = λ inc {ρA} {ρB} {ρC} ρR σ pr →
                         PEq.trans (PEq.sym (SubstRen.fusion (ρA σ pr) (λ _ _ → PEq.refl)))
                                   (PEq.cong (Renaming ⊨⟦_⟧ inc) (ρR σ pr))
         ; R⟦var⟧    = λ v ρR → ρR _ v
         ; embedBC   = PEq.refl }

ifteRenNorm :
      {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
      {ρA : Δ [ flip _∈_ ] Γ} {ρB : Θ [ _⊨^βιξη_ ] Δ}
      {ρC : Θ [ _⊨^βιξη_ ] Γ} →
      (ρR : (σ : ty) (pr : σ ∈ Γ) → EQREL Θ σ (ρB σ (ρA σ pr)) (ρC σ pr)) →
      Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ b ⟧ ρA) ⟧ ρB ≡
      Normalise^βιξη ⊨⟦ b ⟧ ρC →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ l ⟧ ρA) ⟧ ρB)
      (Normalise^βιξη ⊨⟦ l ⟧ ρC) →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ r ⟧ ρA) ⟧ ρB)
      (Normalise^βιξη ⊨⟦ r ⟧ ρC) →
      EQREL Θ σ
      (Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ `ifte b l r ⟧ ρA) ⟧ ρB)
      (Normalise^βιξη ⊨⟦ `ifte b l r ⟧ ρC)
ifteRenNorm b l r {ρA} {ρB} {ρC} ρR eqb eql eqr
  with Normalise^βιξη ⊨⟦ Renaming ⊨⟦ b ⟧ ρA ⟧ ρB
     | Normalise^βιξη ⊨⟦ b ⟧ ρC
ifteRenNorm b l r ρR PEq.refl eql eqr | `embed t | `embed .t =
  reflect^EQREL _ (PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ PEq.refl (reify^EQREL _ eql)) (reify^EQREL _ eqr))
ifteRenNorm b l r ρR () eql eqr | `embed t | `tt
ifteRenNorm b l r ρR () eql eqr | `embed t | `ff
ifteRenNorm b l r ρR () eql eqr | `tt | `embed t
ifteRenNorm b l r ρR PEq.refl eql eqr | `tt | `tt = eql
ifteRenNorm b l r ρR () eql eqr | `tt | `ff
ifteRenNorm b l r ρR () eql eqr | `ff | `embed t
ifteRenNorm b l r ρR () eql eqr | `ff | `tt
ifteRenNorm b l r ρR PEq.refl eql eqr | `ff | `ff = eqr
\end{code}}

These four lemmas are usually painfully proven one after the other. Here
we managed to discharge them by simply instantiating our framework four
times in a row, using the former instances to discharge the constraints
arising in the later ones. But we are not at all limited to proving
statements about \AR{Syntactic}s only.

\subsubsection{Example of Fusable Semantics}

The most simple example of \AR{Fusable} \AR{Semantics} involving a non
\AR{Syntactic} one is probably the proof that \AR{Renaming} followed
by \AR{Normalise^{βιξη}} is equivalent to Normalisation by Evaluation
where the environment has been tweaked.

\begin{code}
RenamingNormaliseFusable :
  Fusable  Renaming
           Normalise^βιξη
           Normalise^βιξη
           (EQREL _ _)
           (λ ρA ρB ρC → ∀ σ pr →
              EQREL _ σ (ρB σ (ρA σ pr)) (ρC σ pr))
           (EQREL _ _)
\end{code}
\AgdaHide{
\begin{code}
RenamingNormaliseFusable =
  record
    { reifyA   = id
    ; Rel𝓔∙  = λ ρR uR → [ uR , ρR ]
    ; Rel𝓔Wk = λ inc ρR → λ σ pr → wk^EQREL σ inc (ρR σ pr)
    ; R⟦var⟧   = λ v ρR → ρR _ v
    ; R⟦$⟧     = λ _ _ _ r → r refl
    ; R⟦λ⟧     = λ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ → tt
    ; R⟦tt⟧    = λ _ → PEq.refl
    ; R⟦ff⟧    = λ _ → PEq.refl
    ; R⟦ifte⟧  = ifteRenNorm
    }


ifteSubstNorm :
     {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
      {ρA : Δ [ _⊢_ ] Γ} {ρB : Θ [ _⊨^βιξη_ ] Δ}
      {ρC : Θ [ _⊨^βιξη_ ] Γ} →
      ((σ₁ : ty) (pr : σ₁ ∈ Δ) → EQREL Θ σ₁ (ρB σ₁ pr) (ρB σ₁ pr)) ×
      ((σ₁ : ty) (pr : σ₁ ∈ Γ) {Θ₁ : Con} (inc : Θ ⊆ Θ₁) →
       EQREL Θ₁ σ₁
       (Normalise^βιξη ⊨⟦ ρA σ₁ pr ⟧
        (λ σ₂ pr₁ → wk^βιξη σ₂ inc $ ρB σ₂ pr₁))
       (wk^βιξη σ₁ inc $ ρC σ₁ pr))
      ×
      ((σ₁ : ty) (pr : σ₁ ∈ Γ) →
       EQREL Θ σ₁ (Normalise^βιξη ⊨⟦ ρA σ₁ pr ⟧ ρB) (ρC σ₁ pr)) →
      Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ b ⟧ ρA) ⟧ ρB ≡
      Normalise^βιξη ⊨⟦ b ⟧ ρC →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ l ⟧ ρA) ⟧ ρB)
      (Normalise^βιξη ⊨⟦ l ⟧ ρC) →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ r ⟧ ρA) ⟧ ρB)
      (Normalise^βιξη ⊨⟦ r ⟧ ρC) →
      EQREL Θ σ
      (Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ `ifte b l r ⟧ ρA) ⟧ ρB)
      (Normalise^βιξη ⊨⟦ `ifte b l r ⟧ ρC)
ifteSubstNorm b l r {ρA} {ρB} {ρC} ρR eqb eql eqr
  with Normalise^βιξη ⊨⟦ Substitution ⊨⟦ b ⟧ ρA ⟧ ρB
     | Normalise^βιξη ⊨⟦ b ⟧ ρC
ifteSubstNorm b l r ρR PEq.refl eql eqr | `embed t | `embed .t =
  reflect^EQREL _ (PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ PEq.refl (reify^EQREL _ eql)) (reify^EQREL _ eqr))
ifteSubstNorm b l r ρR () eql eqr | `embed t | `tt
ifteSubstNorm b l r ρR () eql eqr | `embed t | `ff
ifteSubstNorm b l r ρR () eql eqr | `tt | `embed t
ifteSubstNorm b l r ρR PEq.refl eql eqr | `tt | `tt = eql
ifteSubstNorm b l r ρR () eql eqr | `tt | `ff
ifteSubstNorm b l r ρR () eql eqr | `ff | `embed t
ifteSubstNorm b l r ρR () eql eqr | `ff | `tt
ifteSubstNorm b l r ρR PEq.refl eql eqr | `ff | `ff = eqr

wk-refl : {Γ : Con} (σ : ty) {T U : Γ ⊨^βιξη σ} →
          EQREL Γ σ T U → EQREL Γ σ (wk^βιξη σ refl T) U
wk-refl `Unit     eq = tt
wk-refl `Bool     eq = PEq.trans (wk^nf-refl _) eq
wk-refl (σ `→ τ)  eq = eq

wk^2 : {Θ Δ Γ : Con} (σ : ty) (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ) {T U : Γ ⊨^βιξη σ} →
       EQREL Γ σ T U → EQREL Θ σ (wk^βιξη σ inc₂ $ wk^βιξη σ inc₁ T) (wk^βιξη σ (trans inc₁ inc₂) U)
wk^2 `Unit     inc₁ inc₂ eq = tt
wk^2 `Bool     inc₁ inc₂ eq = PEq.trans (wk^nf-trans inc₁ inc₂ _) (PEq.cong (wk^nf (trans inc₁ inc₂)) eq)
wk^2 (σ `→ τ)  inc₁ inc₂ eq = λ inc₃ → eq (trans inc₁ $ trans inc₂ inc₃)
\end{code}}

Finally, we use the framework to prove that to \AR{Normalise^{βιξη}} by
Evaluation after a \AR{Substitution} amounts to normalising the original
term where the substitution has been evaluated first. The constraints
imposed on the environments might seem quite restrictive but they are
actually similar to the Uniformity condition described by Coquand~\cite{coquand2002formalised}
in her detailled account of Normalisation by Evaluation for a simply-typed
λ-calculus with explicit substitutions.


\begin{code}
SubstitutionNormaliseFusable :
  Fusable  Substitution
           Normalise^βιξη
           Normalise^βιξη
           (EQREL _ _)
           (λ ρA ρB ρC → ((σ : ty) (pr : σ ∈ _) → EQREL _ σ (ρB σ pr) (ρB σ pr))
                      × ((σ : ty) (pr : σ ∈ _) {Θ : Con} (inc : _ ⊆ Θ) →
                         EQREL Θ σ (Normalise^βιξη ⊨⟦ ρA σ pr ⟧ (λ σ pr → wk^βιξη σ inc $ ρB σ pr))
                                   (wk^βιξη σ inc $ ρC σ pr))
                      × ((σ : ty) (pr : σ ∈ _) → EQREL _ σ (Normalise^βιξη ⊨⟦ ρA σ pr ⟧ ρB) (ρC σ pr)))
           (EQREL _ _)
\end{code}
\AgdaHide{
\begin{code}
SubstitutionNormaliseFusable =
  let module RenNorm = Fusion RenamingNormaliseFusable
      module EqNorm  = Synchronised SynchronisableNormalise in
  record
    { reifyA   = id
    ; Rel𝓔∙  = λ {_} {_} {_} {_} {ρA} {ρB} {ρC} ρR uR →
                     [ reflEQREL _ uR , proj₁ ρR ]
                   , [ (λ {Θ} inc → wk^EQREL _ inc uR)
                     , (λ σ pr {Θ} inc →
                       transEQREL σ (RenNorm.fusion (ρA σ pr)
                                                    (λ σ pr → wk^EQREL σ inc (proj₁ ρR σ pr)))
                                    ((proj₁ ∘ proj₂) ρR σ pr inc)) ]
                     , [ uR , (λ σ pr → transEQREL σ (RenNorm.fusion (ρA σ pr) (proj₁ ρR))
                                          ((proj₂ ∘ proj₂) ρR σ pr)) ]
    ; Rel𝓔Wk = λ inc {ρA} ρR →
                            (λ σ pr → wk^EQREL σ inc (proj₁ ρR σ pr))
                          , (λ σ pr {Θ} inc′ →
                               transEQREL σ (EqNorm.lemma (ρA σ pr)
                               (λ σ pr → transEQREL σ (wk^2 σ inc inc′ (proj₁ ρR σ pr))
                                                      (wk^EQREL σ (trans inc inc′) (proj₁ ρR σ pr))))
                               (transEQREL σ ((proj₁ ∘ proj₂) ρR σ pr (trans inc inc′))
                               (symEQREL σ (wk^2 σ inc inc′ (reflEQREL σ (symEQREL σ $ (proj₂ ∘ proj₂) ρR σ pr))))))
                          , (λ σ pr → (proj₁ ∘ proj₂) ρR σ pr inc)
    ; R⟦var⟧   = λ v ρR → (proj₂ ∘ proj₂) ρR _ v
    ; R⟦$⟧     = λ _ _ _ r → r refl
    ; R⟦λ⟧     = λ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ → tt
    ; R⟦tt⟧    = λ _ → PEq.refl
    ; R⟦ff⟧    = λ _ → PEq.refl
    ; R⟦ifte⟧  = ifteSubstNorm
    }
\end{code}}


\section{Conclusion}

We have explained how to make using an inductive family to only
represent terms which are well-scoped and well-typed by construction
more tractable by factoring out a common notion of \AR{Semantics}
encompassing a wide range of type and scope preserving traversals.
This approach crucially relies on the distinction we make between
values in the environment and values in the model, the Kripke
structure associated to binders and the fact that the semantic
counterpart of these binders are supplied with \emph{environment}
values.

We then demonstrated that these traversals being defined using a
common framework becomes a blessing when proving their properties.
We can indeed prove them generically over all well-behaved \AR{Semantics}
and instantiate the corresponding fundamental lemmas to the particular
cases we are interested in.


\bibliography{main}

\end{document}
