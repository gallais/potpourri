%%%% Pick one of the three
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
generalising Goguen and McKinna's ``Candidates for Substitution''
approach to defining one traversal generic enough to be instantiated
to renaming first and then substitution. Its careful distinction of
environment and model values as well as its variation on a structure
typical of a Kripke semantics make it capable of expressing renaming
and substitution but also various forms of Normalisation by Evaluation
and, perhaps more surprisingly, monadic computations such
as a printing function.

We then demonstrate that expressing these algorithms in a common
framework yields immediate benefits: we can deploy some logical
relations generically over these instances and obtain for instance
the fusion lemmas for renaming, substitution and normalisation by
evaluation as simple corollaries of the appropriate fundamental
lemma. All of this work has been formalised in Agda.
\end{abstract}

\section*{Introduction}

In order to implement an embedded Domain Specific Language (eDSL)~\cite{hudak1996building},
a developer can opt for either a shallow or a deep
embedding~\cite{svenningsson2013combining,gill2014domain}. In the shallow approach, she
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
enforcing these invariants in its indices.

Goguen and McKinna's Candidates for Substitution~\cite{goguen1997candidates}
begot work by McBride~\cite{mcbride2005type} in Epigram~\cite{mcbride2004view}
and Benton, Hur, Kennedy and McBride~\cite{benton2012strongly} in Coq~\cite{Coq:manual}
showing how to alleviate the programmer's burden when she opts for the strongly-typed
approach based on inductive families. They both define a traversal generic enough to
be instantiated to renaming first and then substitution. In Benton et al., the bulk
of the work has to be repeated when defining Normalisation by Evaluation. Reasoning
about these definitions is still mostly done in an ad-hoc manner: Coq's tactics
do help them to discharge the four fusion lemmas involving renaming and substitution,
but the same work has to be repeated when studying the evaluation function. They
choose to prove the evaluation function correct by using propositional equality and
assuming function extensionality rather than resorting to the traditional Partial
Equivalence Relation approach we use.

We build on these insights and define an abstract notion of \AR{Semantics}
encompassing these two important operations as well as others Carette et al.
could represent (e.g. measuring the size of a term) and even Normalisation
by Evaluation~\cite{berger1991inverse}. By highlighting the common structure
of all of these algorithms, we get the opportunity to not only implement
them but also prove their properties generically.

\paragraph{Outline} We shall start by defining the simple calculus we will use
as a running example. We will then introduce a notion of environments as well
as one well-known instance: the preorder of renamings. This will lead
us to defining a generic notion of type and scope-preserving \AR{Semantics}
together with a generic evaluation function. We will then showcase the
ground covered by these \AR{Semantics}: from the syntactic ones corresponding
to renaming and substitution to printing with names or some variations on Normalisation
by Evaluation. Finally, we will demonstrate how, the definition of \AR{Semantics}
being generic enough, we can prove fundamental lemmas about these evaluation
functions: we characterise the semantics which are synchronisable and give an
abstract treatment of composition yielding compaction and reuse of proofs
compared to Benton et al.~\cite{benton2012strongly}

\paragraph{Notations} This article is a literate Agda file typeset using the
\LaTeX{} backend with as little post-processing as possible: we simply hide
telescopes of implicit arguments as well as \APT{Set} levels and properly display (super / sub)-scripts
as well as special operators such as \AF{>>=} or \AF{++}. As such, a lot of
the notations have a meaning in Agda: \AIC{green} identifiers are data constructors,
\ARF{pink} names refer to record fields, and \AF{blue} is characteristic of
defined symbols. Underscores have a special status: when defining mixfix
identifiers~\cite{danielsson2011parsing}, they mark positions where arguments
may be inserted; our using the development version of Agda means that we have
access to Haskell-style sections i.e. one may write \AF{\_+} \AN{5} for the partial
application of \AF{\_+\_} corresponding to \AS{λ} \AB{x} \AS{→} \AB{x} \AF{+} \AN{5}
or, to mention something that we will use later on, \AF{Renaming} \AF{⊨⟦\_⟧\_}
for the partial application of \AF{\_⊨⟦\_⟧\_} to \AF{Renaming}.

\paragraph{Formalisation} This whole development has been checked by Agda~\cite{norell2009dependently}
which guarantees that all constructions are indeed well-typed, and all functions are
total. Nonetheless, it should be noted that the generic model constructions and the
various examples of \AR{Semantics} given here can be fully replicated in Haskell using
type families, higher rank polymorphism and generalised algebraic data types to build
singletons~\cite{eisenberg2013dependently} providing the user with the runtime descriptions
of their types or their contexts' shapes. This yields, to the best of our knowledge, the
first tagless and typeful implementation of Normalisation by Evaluation in Haskell. The
subtleties of working with dependent types in Haskell~\cite{lindley2014hasochism} are
outside the scope of this paper but we do provide a (commented) Haskell module containing
all the translated definitions. It should be noted that Danvy, Keller and Puech have achieved
a similar goal in OCaml~\cite{danvytagless} but their formalisation uses parametric higher
order abstract syntax~\cite{chlipala2008parametric} which frees them from having to deal
with variable binding, contexts and use models à la Kripke. However we consider these to be
primordial: they can still guide the implementation of more complex type theories where,
until now, being typeful is still out of reach. Type-level guarantees about scope preservation
can help root out bugs related to fresh name generation, name capture or arithmetic on de
Bruijn levels to recover de Bruijn indices.


\AgdaHide{
\begin{code}
{-# OPTIONS --no-eta #-}
module models where

open import Level using (Level ; _⊔_)
open import Data.Empty
open import Data.Unit renaming (tt to ⟨⟩)
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
with \AIC{`Bool} and \AIC{`Unit} as base types. This serves as a minimal example
of a system with a sum type and a record type equipped with an η-rule. 

\AgdaHide{
\begin{code}
infixr 20 _`→_
infixl 10 _∙_
infix 5 _∈_
infixr 5 1+_
\end{code}}
%<*ty>
\begin{code}
data ty : Set where
  `Unit  : ty
  `Bool  : ty
  _`→_   : (σ τ : ty) → ty
\end{code}
%</ty>

In order to be able to talk about the types of the variables in scope, we
need a notion of contexts. We choose to represent them as snoc lists of
types; \AIC{ε} denotes the empty context and \AB{Γ} \AIC{∙} \AB{σ} the
context \AB{Γ} extended with a fresh variable of type \AB{σ}. Variables
are then positions in such a context represented as typed de Bruijn
indices~\cite{de1972lambda}.

\begin{minipage}[t]{0.5\textwidth}
%<*context>
\begin{code}
data Con : Set where
  ε    : Con
  _∙_  : Con → ty → Con
\end{code}
%</context>
\end{minipage}
\begin{minipage}[t]{0.5\textwidth}
%<*var>
\begin{code}
data _∈_ (σ : ty) : Con → Set where
  zero  : {Γ : Con} → σ ∈ (Γ ∙ σ)
  1+_   : {Γ : Con} {τ : ty} → σ ∈ Γ → σ ∈ (Γ ∙ τ)
\end{code}
%</var>
\end{minipage}

The syntax for this calculus is designed to guarantee that terms are
well-scoped and well-typed by construction. This presentation due to
Altenkirch and Reus~\cite{altenkirch1999monadic} relies heavily on
Dybjer's inductive families~\cite{dybjer1991inductive}. Rather than
having untyped pre-terms and a typing relation assigning a type to
them, the typing rules are here enforced in the syntax: we can see for
example that the \AIC{`var} constructor takes a typed de Bruijn index;
that application (\AIC{\_`\$\_}) ensures that the domain of the function
coincides with the type of its argument; that the body of a λ-abstraction
(\AIC{`λ}) is defined in a context extended with a fresh variable whose
type corresponds to the domain of the function; or that the two branches
of a conditional (\AIC{`ifte}) need to have the same type.

\AgdaHide{
\begin{code}
open import Data.Nat as ℕ using (ℕ ; _+_)

size : Con → ℕ
size ε        = 0
size (Γ ∙ _)  = 1 + size Γ

infix 5 _⊢_
infixl 5 _`$_
\end{code}}
%<*term>
\begin{code}
data _⊢_ (Γ : Con) : (σ : ty) → Set where
  `var     : {σ : ty} (v : σ ∈ Γ) → Γ ⊢ σ
  _`$_     : {σ τ : ty} (t : Γ ⊢ (σ `→ τ)) (u : Γ ⊢ σ) → Γ ⊢ τ
  `λ       : {σ τ : ty} (t : Γ ∙ σ ⊢ τ) → Γ ⊢ (σ `→ τ)
  `⟨⟩      : Γ ⊢ `Unit
  `tt `ff  : Γ ⊢ `Bool
  `ifte    : {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ) → Γ ⊢ σ
\end{code}
%</term>
\section{A Generic Notion of Environment}

All the semantics we are interested in defining associate to a term \AB{t}
of type \AB{Γ} \AD{⊢} \AB{σ}, a value of type \AB{𝓜} \AB{Γ} \AB{σ} given
an interpretation \AB{𝓔} \AB{Δ} {τ} for each one of its free variables
\AB{τ} in \AB{Γ}. We call the collection of these interpretations an
\AB{𝓔}-(evaluation) environment. We leave out \AB{𝓔} when it can easily
be inferred from the context.

The content of environments may vary wildly between different semantics:
when defining renaming, the environments will carry variables whilst the
ones used for normalisation by evaluation contain elements of the model.
But their structure stays the same which prompts us to define the notion
generically. Formally, this translates to \AB{𝓔}-environments being the
pointwise lifting of the relation \AB{𝓔} between contexts and types to a
relation between two contexts. Rather than using a datatype to represent
such a lifting, we choose to use a function space. This decision is based
on Jeffrey's observation that one can obtain associativity of append for
free by using difference lists~\cite{jeffrey2011assoc}. In our case the
interplay between various combinators (e.g. \AF{refl} and \AF{trans})
defined later on is vastly simplified by this rather simple decision.

\AgdaHide{
\begin{code}
infix 5 _[_]_
\end{code}}
%<*environment>
\begin{code}
_[_]_ :  {ℓ : Level} (Δ : Con) (𝓔 : (Δ : Con) (σ : ty) → Set ℓ) (Γ : Con) → Set ℓ
Δ [ 𝓔 ] Γ = (σ : ty) (v : σ ∈ Γ) → 𝓔 Δ σ
\end{code}
%</environment>

\AgdaHide{
\begin{code}
infixl 10 [_]_`∙_
\end{code}}

For a fixed context \AB{Δ} and relation \AB{𝓔}, these environments can
be built step by step by noticing that the environment corresponding to
an empty context is trivial and that one may extend an already existing
environment provided a proof of the right type. In concrete cases, there
will be no sensible way to infer \AB{𝓔} when using the second combinator
hence our decision to make it possible to tell Agda which relation we are
working with.

\noindent\begin{minipage}[t]{0.25\textwidth}
\begin{code}
`ε : {ℓ : Level} {Δ : Con} {𝓔 : (Δ : Con) (σ : ty) → Set ℓ} → Δ [ 𝓔 ] ε
`ε = λ _ ()
\end{code}
\end{minipage}
\begin{minipage}[t]{0.75\textwidth}
\begin{code}
[_]_`∙_ :  {ℓ : Level} {Γ Δ : Con} (𝓔 : Con → ty → Set ℓ) {σ : ty} → Δ [ 𝓔 ] Γ → 𝓔 Δ σ → Δ [ 𝓔 ] (Γ ∙ σ)
([ 𝓔 ] ρ `∙ s) _ zero    = s
([ 𝓔 ] ρ `∙ s) σ (1+ n)  = ρ σ n
\end{code}
\end{minipage}

\paragraph{The Preorder of Renamings}\label{preorder}
A key instance of environments playing a predominant role in this paper
is the notion of renaming. The reader may be accustomed to the more
restrictive notion of context inclusions as described by Order Preserving
Embeddings~\cite{altenkirch1995categorical}. Writing non-injective or
non-order preserving renamings would take perverse effort given that we
only implement generic interpretations. In practice, the only combinators
we use do guarantee that all the renamings we generate are context inclusions.
As a consequence, we will use the two expressions interchangeably from now
on.

A context inclusion \AB{Γ} \AF{⊆} \AB{Δ} is an environment pairing each
variable of type \AB{σ} in \AB{Γ} to one of the same type in \AB{Δ}.

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
principle'', we mean that if \AB{P} holds of \AB{Γ} and \AB{Γ} \AF{⊆} \AB{Δ}
then \AB{P} holds for \AB{Δ} too.
In the case of variables, weakening merely corresponds to applying the
renaming function in order to obtain a new variable. The environments'
case is also quite simple: being a pointwise lifting of a relation \AB{𝓔}
between contexts and types, they enjoy weakening if \AB{𝓔} does.

\noindent\begin{minipage}[t]{0.4\textwidth}
\begin{code}
wk^∈ : {Δ Γ : Con} {σ : ty} → Γ ⊆ Δ → σ ∈ Γ → σ ∈ Δ
wk^∈ inc pr = inc _ pr
\end{code}
\end{minipage}
\begin{minipage}[t]{0.60\textwidth}
\begin{code}
wk[_] :  {ℓ : Level} {Δ : Con} {𝓔 : (Δ : Con) (σ : ty) → Set ℓ} (wk : {Θ : Con} {σ : ty} (inc : Δ ⊆ Θ) → 𝓔 Δ σ → 𝓔 Θ σ)
         {Γ Θ : Con} → Δ ⊆ Θ → Δ [ 𝓔 ] Γ →  Θ [ 𝓔 ] Γ
wk[ wk ] inc ρ = λ σ pr → wk inc $ ρ σ pr
\end{code}
\end{minipage}

These simple observations allow us to prove that context inclusions
form a preorder which, in turn, lets us provide the user with the
constructors Altenkirch, Hofmann and Streicher's ``Category of
Weakenings"~\cite{altenkirch1995categorical} is based on.

\noindent\begin{minipage}[t]{0.3\textwidth}
\begin{code}
refl : {Γ : Con} → Γ ⊆ Γ
refl = λ _ → id
\end{code}
\end{minipage}
\begin{minipage}[t]{0.7\textwidth}
\begin{code}
trans : {Γ Δ Θ : Con} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ) → Γ ⊆ Θ
trans inc₁ inc₂ = wk[ wk^∈ ] inc₂ inc₁
\end{code}
\end{minipage}

\noindent\begin{minipage}[t]{0.5\textwidth}
\begin{code}
step : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) → Γ ⊆ (Δ ∙ σ)
step inc = trans inc $ λ _ → 1+_
\end{code}
\end{minipage}
\begin{minipage}[t]{0.5\textwidth}
\begin{code}
pop! : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) → (Γ ∙ σ) ⊆ (Δ ∙ σ)
pop! inc = [ flip _∈_ ] step inc `∙ zero
\end{code}
\end{minipage}

Now that we are equipped with the notion of inclusion, we have all
the pieces necessary to describe the Kripke structure of our models
of the simply-typed λ-calculus.

\section{Semantics and Generic Evaluation Functions}

The upcoming sections are dedicated to demonstrating that renaming,
substitution, printing with names, and normalisation by evaluation all
share the same structure. We start by abstracting away a notion of
\AR{Semantics} encompassing all these constructions. This approach
will make it possible for us to implement a generic traversal
parametrised by such a \AR{Semantics} once and for all and to focus
on the interesting model constructions instead of repeating the same
pattern over and over again.

A \AR{Semantics} is indexed by two relations \AB{𝓔} and \AB{𝓜}
describing respectively the values in the environment and the ones
in the model. In cases such as substitution or normalisation by
evaluation, \AB{𝓔} and \AB{𝓜} will happen to coincide but keeping
these two relations distinct is precisely what makes it possible
to go beyond these and also model renaming or printing with names.
The record packs the properties of these relations necessary to
define the evaluation function.

\begin{code}
record Semantics {ℓ^E ℓ^M : Level} (𝓔 : Con → ty → Set ℓ^E) (𝓜 : Con → ty → Set ℓ^M) : Set (ℓ^E ⊔ ℓ^M) where
\end{code}
\AgdaHide{
\begin{code}
  infixl 5 _⟦$⟧_
  field
\end{code}}

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
case corresponds to the intuition that the environment attaches
interpretations to the variables in scope: it guarantees that one
can turn a value from the environment into a model one. The traversal
will therefore be able to, when hitting a variable, lookup the
corresponding value in the environment and return it.

\begin{code}
    ⟦var⟧   :  {Γ : Con} {σ : ty} (v : 𝓔 Γ σ) → 𝓜 Γ σ
\end{code}

The semantic λ-abstraction is notable for two reasons: first, following
Mitchell and Moggi~\cite{mitchell1991kripke}, its structure is typical
of models à la Kripke allowing arbitrary extensions of the context; and
second, instead of being a function in the host language taking values
in the model as arguments, it is a function that takes \emph{environment}
values. Indeed, the body of a λ-abstraction exposes one extra free variable
thus prompting us to extend the evaluation environment with an additional
value. This slight variation in the type of semantic λ-abstraction
guarantees that such an argument will be provided to us.

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

The fundamental lemma of semantics is then proven in a module indexed by
a \AF{Semantics}, which would correspond to using a Section in Coq. It is
defined by structural recursion on the term. Each constructor is replaced
by its semantic counterpart in order to combine the induction hypotheses
for its subterms. In the λ-abstraction case, the type of \ARF{⟦λ⟧} guarantees,
in a fashion reminiscent of Normalisation by Evaluation, that the semantic
argument can be stored in the environment which will have been weakened
beforehand.

\begin{code}
module Eval {ℓ^E ℓ^M : Level} {𝓔 : (Γ : Con) (σ : ty) → Set ℓ^E} {𝓜 : (Γ : Con) (σ : ty) → Set ℓ^M} (𝓢 : Semantics 𝓔 𝓜) where
  open Semantics 𝓢
\end{code}\vspace{-2.5em}%ugly but it works!
\AgdaHide{
\begin{code}
  infix 10 _⊨⟦_⟧_ _⊨eval_
\end{code}}
%<*evaluation>
\begin{code}
  lemma : {Δ Γ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ 𝓔 ] Γ) → 𝓜 Δ σ
  lemma (`var v)       ρ = ⟦var⟧ $ ρ _ v
  lemma (t `$ u)       ρ = lemma t ρ ⟦$⟧ lemma u ρ
  lemma (`λ t)         ρ = ⟦λ⟧ λ inc u → lemma t $ [ 𝓔 ] wk[ wk ] inc ρ `∙ u
  lemma `⟨⟩            ρ = ⟦⟨⟩⟧
  lemma `tt            ρ = ⟦tt⟧
  lemma `ff            ρ = ⟦ff⟧
  lemma (`ifte b l r)  ρ = ⟦ifte⟧ (lemma b ρ) (lemma l ρ) (lemma r ρ)
\end{code}
%</evaluation>

We introduce \AF{\_⊨⟦\_⟧\_} as an alternative name for the fundamental
lemma and \AF{\_⊨eval\_} for the special case where we use \ARF{embed}
to generate a diagonal environment of type \AB{Γ} \AF{[} \AB{𝓔} \AF{]}
\AB{Γ}. We open the module \AM{Eval} unapplied thus discharging (λ-lifting)
its members over the \AR{Semantics} parameter. This means that a partial
application of \AF{\_⊨⟦\_⟧\_} will correspond to the specialisation of the
fundamental lemma to a given semantics. \AB{𝓢} \AF{⊨⟦} \AB{t} \AF{⟧} \AB{ρ}
is meant to convey the idea that the semantics \AB{𝓢} is used to evaluate
the term \AB{t} in the environment \AB{ρ}. Similarly, \AB{𝓢} \AF{⊨eval}
\AB{t} is meant to denote the evaluation of the term \AB{t} in the semantics
\AB{𝓢} (using a diagonal environment).

\noindent\begin{minipage}[t]{0.55\textwidth}
\begin{code}
  _⊨⟦_⟧_ : {Δ Γ : Con} {σ : ty} → Γ ⊢ σ → Δ [ 𝓔 ] Γ → 𝓜 Δ σ
  _⊨⟦_⟧_ = lemma
\end{code}
\end{minipage}
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  _⊨eval_ : {Γ : Con} {σ : ty} → Γ ⊢ σ → 𝓜 Γ σ
  _⊨eval_ t = _⊨⟦_⟧_ t embed
\end{code}
\AgdaHide{
\begin{code}
open Eval hiding (lemma) public
\end{code}}
\end{minipage}

The diagonal environment generated using \ARF{embed} when defining the
\AF{\_⊨eval\_} function lets us kickstart the evaluation of arbitrary
\emph{open} terms. In the case of printing with names, this corresponds to
picking a naming scheme for free variables whilst in the usual model
construction used to perform normalisation by evaluation, it corresponds
to η-expanding the variables.

\section{Syntax is the Identity Semantics}

As we have explained earlier, this work has been directly influenced by
McBride's manuscript~\cite{mcbride2005type}. It seems appropriate
to start our exploration of \AR{Semantics} with the two operations he
implements as a single traversal. We call these operations syntactic
because the values in the model are actual terms and almost all term
constructors are kept as their own semantic counterpart. As observed by
McBride, it is enough to provide three operations describing the properties
of the values in the environment to get a full-blown \AR{Semantics}. This
fact is witnessed by our simple \AR{Syntactic} record type together with
the \AF{syntactic} function turning its inhabitants into associated
\AR{Semantics}.

%<*syntactic>
\begin{code}
record Syntactic {ℓ : Level} (𝓔 : (Γ : Con) (σ : ty) → Set ℓ) : Set ℓ where
  field  embed  : {Γ : Con} (σ : ty) → σ ∈ Γ → 𝓔 Γ σ
         wk     : {Γ Δ : Con} {σ : ty} → Γ ⊆ Δ → 𝓔 Γ σ → 𝓔 Δ σ
         ⟦var⟧  : {Γ : Con} {σ : ty} → 𝓔 Γ σ → Γ ⊢ σ
\end{code}\vspace{-1.5em}%ugly but it works!
%</syntactic>
\begin{code}
syntactic : {ℓ : Level} {𝓔 : (Γ : Con) (σ : ty) → Set ℓ} (syn : Syntactic 𝓔) → Semantics 𝓔 _⊢_
syntactic syn = let open Syntactic syn in record
  { wk      = wk; embed   = embed; ⟦var⟧   = ⟦var⟧
  ; ⟦λ⟧     = λ t → `λ $ t (step refl) $ embed _ zero
  ; _⟦$⟧_   = _`$_; ⟦⟨⟩⟧ = `⟨⟩; ⟦tt⟧ = `tt; ⟦ff⟧ = `ff; ⟦ifte⟧  = `ifte }
\end{code}

The shape of \ARF{⟦λ⟧} or \ARF{⟦⟨⟩⟧} should not trick the reader
into thinking that this definition performs some sort of η-expansion:
\AF{lemma} indeed only ever uses one of these when the evaluated term's
head constructor is already respectively a \AIC{`λ} or a \AIC{`⟨⟩}.
It is therefore absolutely possible to define renaming or substitution
using this approach. We can now port McBride's definitions to our
framework.

\paragraph{Functoriality, also known as Renaming}
Our first example of a \AR{Syntactic} operation works with variables as
environment values. As a consequence, embedding is trivial; we have already
defined weakening earlier (see Section \ref{preorder}) and we can turn
a variable into a term by using the \AIC{`var} constructor.

\begin{code}
syntacticRenaming : Syntactic (flip _∈_)
syntacticRenaming = record { embed = λ _ → id; wk = wk^∈; ⟦var⟧ = `var }

Renaming : Semantics (flip _∈_) _⊢_; Renaming = syntactic syntacticRenaming
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

\paragraph{Simultaneous Substitution}
Our second example of a semantics is another spin on the syntactic model:
the environment values are now terms. We can embed variables into environment
values by using the \AIC{`var} constructor and we inherit weakening for terms
from the previous example.

\begin{code}
syntacticSubstitution : Syntactic _⊢_
syntacticSubstitution = record { embed = λ _ → `var; wk = wk^⊢; ⟦var⟧ = id }

Substitution : Semantics _⊢_ _⊢_; Substitution = syntactic syntacticSubstitution
\end{code}

Because the diagonal environment used by \AF{Substitution} \AF{⊨eval\_}
is obtained by \ARF{embed}ding membership proofs into terms using the
\AIC{`var} constructor, we get yet another definition of the identity
function on terms. The semantic function \AF{Substitution} \AF{⊨⟦\_⟧\_}
is once again more interesting: it is an implementation of simultaneous
substitution.

\begin{code}
subst : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊢_ ] Γ) → Δ ⊢ σ
subst = Substitution ⊨⟦_⟧_
\end{code}

\section{Printing with Names}
\label{prettyprint}

Before considering the various model constructions involved in defining
normalisation functions deciding different equational theories, let us
make a detour to a perhaps slightly more surprising example of a
\AF{Semantics}: printing with names. A user-facing project would naturally
avoid directly building a \AD{String} and rather construct an inhabitant of
a more sophisticated datatype in order to generate a prettier output~\cite{hughes1995design,wadler2003prettier}.
But we stick to the simpler setup as pretty printing is not our focus here.


This example is quite interesting for two reasons. Firstly, the distinction
between the type of values in the environment and the ones in the model is
once more instrumental in giving the procedure a precise type guiding our
implementation. Indeed, the environment carries \emph{names} for the variables
currently in scope whilst the inhabitants of the model are \emph{computations}
threading a stream to be used as a source of fresh names every time a new variable
is introduced by a λ-abstraction. If the values in the environment were allowed
to be computations too, we would not root out all faulty implementations: the
typechecker would for instance quite happily accept a program picking a new
name every time a variable appears in the term.

\AgdaHide{
\begin{code}
open import Data.Char using (Char)
open import Data.String hiding (show)
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
record Name (Γ : Con) (σ : ty) : Set where
  constructor mkName
  field runName : String

record Printer (Γ : Con) (σ : ty) : Set where
  constructor mkPrinter
  field runPrinter : State (Stream String) String
\end{code}
\AgdaHide{
\begin{code}
open Name
open Printer
\end{code}}

Secondly, the fact that values in the model are computations and that this
poses no problem whatsoever in this framework means it is appropriate for
handling languages with effects~\cite{moggi1991notions}, or effectful
semantics e.g. logging the various function calls. Here is the full definition
of the printer assuming the existence of \AF{formatλ}, \AF{format\$}, and
\AF{formatIf} picking a way to display these constructors.

\AgdaHide{
\begin{code}
formatλ : String → String → String
formatλ x b = "λ" ++ x ++ ". " ++ b

format$ : String → String → String
format$ f t = f ++ " (" ++ t ++ ")"

formatIf : String → String → String → String
formatIf b l r = "if (" ++ b  ++ ") then (" ++ l ++ ") else (" ++ r ++ ")"
\end{code}}
\begin{code}
Printing : Semantics Name Printer
Printing = record
  { embed   = λ _ → mkName ∘ show ∘ deBruijn
  ; wk      = λ _ → mkName ∘ runName
  ; ⟦var⟧   = mkPrinter ∘ return ∘ runName
  ; _⟦$⟧_   =  λ mf mt → mkPrinter $ format$ <$> runPrinter mf ⊛ runPrinter mt
  ; ⟦λ⟧     =  λ {_} {σ} mb → mkPrinter $ get >>= λ names → let `x` = head names in
               put (tail names)                                  >>= λ _ →
               runPrinter (mb (step {σ = σ} refl) (mkName `x`))  >>= λ `b` →
               return $ formatλ `x` `b`
  ; ⟦⟨⟩⟧    = mkPrinter $ return "⟨⟩"
  ; ⟦tt⟧    = mkPrinter $ return "tt"
  ; ⟦ff⟧    = mkPrinter $ return "ff"
  ; ⟦ifte⟧  =  λ mb ml mr → mkPrinter $
               formatIf <$> runPrinter mb ⊛ runPrinter ml ⊛ runPrinter mr }
\end{code}

Our definition of \ARF{embed} erases the membership proofs to
recover the corresponding de Bruijn indices which are then turned
into strings using \AF{show}, defined in Agda's standard library.
This means that, using \AF{Printing} \AF{⊨eval\_}, the free
variables will be displayed as numbers whilst the bound ones will
be given names taken from the name supply. This is quite clearly
a rather crude name generation strategy and our approach to naming
would naturally be more sophisticated in a user-facing language.
We can for instance imagine that the binders arising from a user
input would carry naming hints based on the name the user picked
and that binders manufactured by the machine would be following
a type-based scheme: functions would be \AB{f}s or \AB{g}s, natural
numbers \AB{m}s, \AB{n}s, etc.

\begin{code}
  where
    deBruijn : {Γ : Con} {σ : ty} → σ ∈ Γ → ℕ
    deBruijn zero    = 0
    deBruijn (1+ n)  = 1 + deBruijn n
\end{code}

We still need to provide a \AD{Stream} of fresh
names to this computation in order to run it. Given that \ARF{embed} erases
free variables to numbers, we'd rather avoid using numbers if we want to
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

Before defining \AF{print}, we introduce \AF{nameContext} (implementation
omitted here) which is a function delivering a stateful computation using
the provided stream of fresh names to generate an environment of names
for a given context. This means that we are now able to define a printing
function using names rather than numbers for the variables appearing free
in a term.

\begin{code}
nameContext : (Δ : Con) (Γ : Con) → State (Stream String) (Δ [ Name ] Γ)
\end{code}
\AgdaHide{
\begin{code}
nameContext Δ ε        =  return $ λ _ ()
nameContext Δ (Γ ∙ σ)  =  nameContext Δ Γ >>= λ g →
                        get >>= λ names → put (tail names) >>
                        return ([ Name ] g `∙ mkName (head names))
\end{code}}\vspace{-2em}%ugly but it works!
\begin{code}
print : {Γ : Con} {σ : ty} (t : Γ ⊢ σ) → String
print {Γ} t = proj₁ $ (nameContext Γ Γ >>= runPrinter ∘ Printing ⊨⟦ t ⟧_) names
\end{code}

We can observe \AF{print}'s behaviour by writing a test.
If we state this test as a propositional equality and prove it using \AIC{refl},
the typechecker will have to check that both expressions indeed compute
to the same value. Here we display a term corresponding to the η-expansion
of the first free variable in the context \AIC{ε} \AIC{∙} (\AB{σ} \AIC{`→} \AB{τ}).
As we can see, it receives the name \AStr{"a"} whilst the binder introduced by
the η-expansion is called \AStr{"b"}.

\begin{code}
pretty$ : {σ τ : ty} → print {Γ = ε ∙ σ `→ τ} (`λ $ `var (1+ zero) `$ `var zero) ≡ "λb. a (b)"
pretty$ = PEq.refl
\end{code}

\section{Normalisation by Evaluation}

Normalisation by Evaluation is a technique exploiting the computational
power of a host language in order to normalise expressions of a deeply
embedded one. The process is based on a model construction describing a
family of types \AB{𝓜} indexed by a context \AB{Γ} and a type \AB{σ}. Two
procedures are then defined: the first one (\AF{eval}) constructs an element
of \AB{𝓜} \AB{Γ} \AB{σ} provided a well-typed term of the corresponding
\AB{Γ} \AD{⊢} \AB{σ} type whilst the second one (\AF{reify}) extracts, in
a type-directed manner, normal forms \AB{Γ} \AD{⊢^{nf}} \AB{σ} from elements
of the model \AB{𝓜} \AB{Γ} \AB{σ}. Normalisation is achieved by composing
the two procedures. The definition of this \AF{eval} function is a natural
candidate for our \AF{Semantics} framework. Normalisation is always defined
for a given equational theory so we are going to start by recalling the
various rules a theory may satisfy.

Thanks to \AF{Renaming} and \AF{Substitution} respectively, we can formally
define η-expansion and β-reduction. The η-rules are saying that for some types,
terms have a canonical form: functions will all be λ-headed whilst record will
be a collection of fields which translates here to all the elements of the
\AIC{`Unit} type being equal to \AIC{`⟨⟩}.

\noindent\begin{minipage}[t]{0.50\textwidth}
\AgdaHide{
\begin{code}
infixl 10 _⟨_/var₀⟩
\end{code}}
\begin{code}
eta : {Γ : Con} {σ τ : ty} (t : Γ ⊢ σ `→ τ) → Γ ⊢ σ `→ τ
eta t = `λ $ wk^⊢ (step refl) t `$ `var zero
\end{code}
\end{minipage}
\begin{minipage}[t]{0.50\textwidth}
\begin{mathpar}
\inferrule{
  }{\text{\AB{t} ↝ \AF{eta} \AB{t}}
  }{η_1}
\and \inferrule{\text{\AB{t} \AgdaSymbol{:} \AB{Γ} \AD{⊢} \AIC{`Unit}}
  }{\text{\AB{t} ↝ \AIC{`⟨⟩}}
  }{η_2}
\end{mathpar}
\end{minipage}

\noindent\begin{minipage}[t]{0.55\textwidth}
\begin{code}
_⟨_/var₀⟩ : {Γ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
t ⟨ u /var₀⟩ = subst t $ [ _⊢_ ] (λ _ → `var) `∙ u
\end{code}
\end{minipage}
\begin{minipage}[t]{0.45\textwidth}
\begin{mathpar}
\inferrule{
  }{\text{(\AIC{`λ} \AB{t}) \AIC{`\$} \AB{u} ↝ \AB{t} \AF{⟨} \AB{u} \AF{/var₀⟩}}
  }{β}
\end{mathpar}
\end{minipage}

The β-rule is the main driving force when it comes to actually computing
but the presence of an inductive data type (\AIC{`Bool}) and its eliminator
(\AIC{`ifte}) means we have an extra opportunity for redexes: whenever the
boolean the eliminator is branching over is in canonical form, we may apply
a ι-rule. Finally, the ξ-rule is the one making it possible to reduce under
λ-abstractions which is the distinction between weak-head normalisation and
strong normalisation.
\begin{mathpar}
\inferrule{
  }{\text{\AIC{`ifte} \AIC{`tt} \AB{l} \AB{r} ↝ \AB{l}}
  }{ι_1}
\and
\inferrule{
  }{\text{\AIC{`ifte} \AIC{`ff} \AB{l} \AB{r} ↝ \AB{r}}
  }{ι_2}
\and
\inferrule{\text{\AB{t} ↝ \AB{u}}
  }{\text{\AIC{`λ} \AB{t} ↝ \AIC{`λ} \AB{u}}
  }{ξ}
\end{mathpar}

Now that we have recalled all these rules, we can talk precisely
about the sort of equational theory decided by the model construction
we choose to perform. We start with the usual definition of Normalisation
by Evaluation which goes under λs and produces η-long βι-short normal
forms.

\subsection{Normalisation by Evaluation for βιξη}
\label{nbe}

In the case of Normalisation by Evaluation, the elements of the model
and the ones carried by the environment will both have the same type:
\AF{\_⊨^{βιξη}\_}, defined by induction on its second argument. In
order to formally describe this construction, we need to have a precise
notion of normal forms. Indeed if the η-rules guarantee that we can
represent functions (respectively inhabitants of \AIC{`Unit}) in the
source language as function spaces (respectively \AR{⊤}) in Agda, there
are no such rules for \AIC{`Bool}ean values which will be represented
as normal forms of the right type i.e. as either \AIC{`tt}, \AIC{`ff}
or a neutral expression.

These normal forms can be formally described by two mutually defined
inductive families: \AD{\_⊢[\_]^{ne}\_} is the type of stuck terms made
up of a variable to which a spine of eliminators in normal forms is
applied; and \AD{\_⊢[\_]^{nf}\_} describes the normal forms. These
families are parametrised by a predicate \AB{R} characterising the
types at which the user is allowed to turn a neutral expression into a
normal form as demonstrated by the constructor \AIC{`embed}'s first argument.

\AgdaHide{
\begin{code}
infix 5 _⊢[_]^ne_ _⊢[_]^nf_
mutual
\end{code}}
\begin{code}
  data _⊢[_]^ne_ (Γ : Con) (R : ty → Set) (σ : ty) : Set where
    `var   : (v : σ ∈ Γ) → Γ ⊢[ R ]^ne σ
    _`$_   : {τ : ty} (t : Γ ⊢[ R ]^ne τ `→ σ) (u : Γ ⊢[ R ]^nf τ) → Γ ⊢[ R ]^ne σ
    `ifte  : (b : Γ ⊢[ R ]^ne `Bool) (l r : Γ ⊢[ R ]^nf σ) → Γ ⊢[ R ]^ne σ

  data _⊢[_]^nf_ (Γ : Con) (R : ty → Set) : (σ : ty) → Set where
    `embed  : {σ : ty} (pr : R σ) (t : Γ ⊢[ R ]^ne σ) → Γ ⊢[ R ]^nf σ
    `⟨⟩     : Γ ⊢[ R ]^nf `Unit
    `tt     : Γ ⊢[ R ]^nf `Bool
    `ff     : Γ ⊢[ R ]^nf `Bool
    `λ      : {σ τ : ty} (b : Γ ∙ σ ⊢[ R ]^nf τ) → Γ ⊢[ R ]^nf (σ `→ τ)
\end{code}

Once more, context inclusions induce the expected notions of weakening \AF{wk^{ne}}
and \AF{wk^{nf}}. We omit their purely structural implementation here and would
thoroughly enjoy doing so in the source file too: our constructions so far have
been syntax-directed and could hopefully be leveraged by a generic account of syntaxes
with binding.

\AgdaHide{
\begin{code}
wk^ne : {Δ Γ : Con} (inc : Γ ⊆ Δ) {R : ty → Set} {σ : ty} (ne : Γ ⊢[ R ]^ne σ) → Δ ⊢[ R ]^ne σ
wk^nf : {Δ Γ : Con} (inc : Γ ⊆ Δ) {R : ty → Set} {σ : ty} (ne : Γ ⊢[ R ]^nf σ) → Δ ⊢[ R ]^nf σ
wk^ne inc (`var v)        = `var $′ wk^∈ inc v
wk^ne inc (ne `$ u)       = wk^ne inc ne `$ wk^nf inc u
wk^ne inc (`ifte ne l r)  = `ifte (wk^ne inc ne) (wk^nf inc l) (wk^nf inc r)

wk^nf inc (`embed pr t) = `embed pr $′ wk^ne inc t
wk^nf inc `⟨⟩           = `⟨⟩
wk^nf inc `tt           = `tt
wk^nf inc `ff           = `ff
wk^nf inc (`λ nf)       = `λ $′ wk^nf (pop! inc) nf

infix 5 [_,_]
[_,_] : {ℓ : Level} {Γ : Con} {τ : ty} {P : (σ : ty) (pr : σ ∈ Γ ∙ τ) → Set ℓ} →
        (p0 : P τ zero) →
        (pS : (σ : ty) (n : σ ∈ Γ) → P σ (1+ n)) →
        (σ : ty) (pr : σ ∈ Γ ∙ τ) → P σ pr
[ p0 , pS ] σ zero    = p0
[ p0 , pS ] σ (1+ n)  = pS σ n

mutual

  wk^nf-refl′ : {Γ : Con} {R : ty → Set} {σ : ty} {f : Γ ⊆ Γ} (prf : (σ : ty) (pr : σ ∈ Γ) → f σ pr ≡ pr) →
                (t : Γ ⊢[ R ]^nf σ) → wk^nf f t ≡ t
  wk^nf-refl′ prf (`embed pr t)  = PEq.cong (`embed pr) $ wk^ne-refl′ prf t
  wk^nf-refl′ prf `⟨⟩            = PEq.refl
  wk^nf-refl′ prf `tt            = PEq.refl
  wk^nf-refl′ prf `ff            = PEq.refl
  wk^nf-refl′ prf (`λ t)         = PEq.cong `λ $ wk^nf-refl′ ([ PEq.refl , (λ σ → PEq.cong 1+_ ∘ prf σ) ]) t

  wk^ne-refl′ : {Γ : Con} {R : ty → Set} {σ : ty} {f : Γ ⊆ Γ} (prf : (σ : ty) (pr : σ ∈ Γ) → f σ pr ≡ pr) →
                (t : Γ ⊢[ R ]^ne σ) → wk^ne f t ≡ t
  wk^ne-refl′ prf (`var v)       = PEq.cong `var $ prf _ v
  wk^ne-refl′ prf (t `$ u)       = PEq.cong₂ _`$_ (wk^ne-refl′ prf t) (wk^nf-refl′ prf u)
  wk^ne-refl′ prf (`ifte b l r)  = PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ (wk^ne-refl′ prf b) (wk^nf-refl′ prf l)) (wk^nf-refl′ prf r)

mutual

  wk^nf-trans′ : {Θ Δ Γ : Con} {R : ty → Set} {σ : ty} {inc₁ : Γ ⊆ Δ} {inc₂ : Δ ⊆ Θ}
                 {f : Γ ⊆ Θ} (prf : (σ : ty) (pr : σ ∈ Γ) → trans inc₁ inc₂ σ pr ≡ f σ pr)
                 (t : Γ ⊢[ R ]^nf σ) →  wk^nf inc₂ (wk^nf inc₁ t) ≡ wk^nf f t
  wk^nf-trans′ prf (`embed pr t)  = PEq.cong (`embed pr) (wk^ne-trans′ prf t)
  wk^nf-trans′ prf `⟨⟩            = PEq.refl
  wk^nf-trans′ prf `tt            = PEq.refl
  wk^nf-trans′ prf `ff            = PEq.refl
  wk^nf-trans′ prf (`λ t)         = PEq.cong `λ $ wk^nf-trans′ ([ PEq.refl , (λ σ → PEq.cong 1+_ ∘ prf σ) ]) t

  wk^ne-trans′ : {Θ Δ Γ : Con} {R : ty → Set} {σ : ty} {inc₁ : Γ ⊆ Δ} {inc₂ : Δ ⊆ Θ}
                 {f : Γ ⊆ Θ} (prf : (σ : ty) (pr : σ ∈ Γ) → trans inc₁ inc₂ σ pr ≡ f σ pr)
                 (t : Γ ⊢[ R ]^ne σ) →  wk^ne inc₂ (wk^ne inc₁ t) ≡ wk^ne f t
  wk^ne-trans′ prf (`var v)       = PEq.cong `var (prf _ v)
  wk^ne-trans′ prf (t `$ u)       = PEq.cong₂ _`$_ (wk^ne-trans′ prf t) (wk^nf-trans′ prf u)
  wk^ne-trans′ prf (`ifte b l r)  = PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ (wk^ne-trans′ prf b) (wk^nf-trans′ prf l)) (wk^nf-trans′ prf r)

wk^nf-refl : {Γ : Con} {R : ty → Set} {σ : ty} (t : Γ ⊢[ R ]^nf σ) → wk^nf refl t ≡ t
wk^nf-refl = wk^nf-refl′ (λ _ _ → PEq.refl)

wk^ne-refl : {Γ : Con} {R : ty → Set} {σ : ty} (t : Γ ⊢[ R ]^ne σ) → wk^ne refl t ≡ t
wk^ne-refl = wk^ne-refl′ (λ _ _ → PEq.refl)

wk^nf-trans : {Θ Δ Γ : Con} {R : ty → Set} {σ : ty} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ)
               (t : Γ ⊢[ R ]^nf σ) →  wk^nf inc₂ (wk^nf inc₁ t) ≡ wk^nf (trans inc₁ inc₂) t
wk^nf-trans inc₁ inc₂ = wk^nf-trans′ (λ _ _ → PEq.refl)

wk^ne-trans : {Θ Δ Γ : Con} {R : ty → Set} {σ : ty} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ)
               (t : Γ ⊢[ R ]^ne σ) →  wk^ne inc₂ (wk^ne inc₁ t) ≡ wk^ne (trans inc₁ inc₂) t
wk^ne-trans inc₁ inc₂ = wk^ne-trans′ (λ _ _ → PEq.refl)
\end{code}}

We now come to the definition of the model. We introduce the predicate
\AF{R^{βιξη}} characterising the types for which we may turn a neutral
expression into a normal form. It is equivalent to the unit type \AR{⊤}
for \AIC{`Bool} and to the empty type \AD{⊥} otherwise. This effectively
guarantees that we use the η-rules eagerly: all inhabitants of
\AB{Γ} \AF{⊢[} \AF{R^{βιξη}} \AF{]^{nf}} \AIC{`Unit} and
\AB{Γ} \AF{⊢[} \AF{R^{βιξη}} \AF{]^{nf}} (\AB{σ} \AIC{`→} \AB{τ}) are
equal to \AIC{`⟨⟩} and a \AIC{`λ}-headed term respectively.

The model construction then follows the usual pattern pioneered by
Berger~\cite{berger1993program} and formally analysed and thoroughly
explained by Catarina Coquand~\cite{coquand2002formalised} in the case
of a simply-typed lambda calculus with explicit substitutions. We proceed by
induction on the type and make sure that η-expansion is applied eagerly: all
inhabitants of \AB{Γ} \AF{⊨^{βιξη}} \AIC{`Unit} are indeed equal and all elements
of \AB{Γ} \AF{⊨^{βιξη}} (\AB{σ} \AIC{`→} \AB{τ}) are functions in Agda.

\begin{minipage}[t]{0.3\textwidth}
\begin{code}
R^βιξη : ty → Set
R^βιξη `Bool  = ⊤
R^βιξη _      = ⊥
\end{code}
\end{minipage}
\begin{minipage}[t]{0.7\textwidth}
\AgdaHide{
\begin{code}
infix 5 _⊨^βιξη_
\end{code}}
%<*sem>
\begin{code}
_⊨^βιξη_ : (Γ : Con) (σ : ty) → Set
Γ ⊨^βιξη `Unit     = ⊤
Γ ⊨^βιξη `Bool     = Γ ⊢[ R^βιξη ]^nf `Bool
Γ ⊨^βιξη (σ `→ τ)  = {Δ : Con} → Γ ⊆ Δ → Δ ⊨^βιξη σ → Δ ⊨^βιξη τ
\end{code}
%</sem>
\end{minipage}

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
model values and normal forms. \AF{reflect^{βιξη}} performs a form of semantical
η-expansion: all stuck \AIC{`Unit} terms have the same image and all stuck functions
are turned into functions in the host language.

\AgdaHide{
\begin{code}
mutual
\end{code}}
\begin{code}
  var‿0^βιξη : {Γ : Con} {σ : ty} → Γ ∙ σ ⊨^βιξη σ
  var‿0^βιξη = reflect^βιξη _ $′ `var zero

  reflect^βιξη : {Γ : Con} (σ : ty) (t : Γ ⊢[ R^βιξη ]^ne σ) → Γ ⊨^βιξη σ
  reflect^βιξη `Unit     t = ⟨⟩
  reflect^βιξη `Bool     t = `embed _ t
  reflect^βιξη (σ `→ τ)  t = λ inc u → reflect^βιξη τ $′ wk^ne inc t `$ reify^βιξη σ u

  reify^βιξη : {Γ : Con} (σ : ty) (T : Γ ⊨^βιξη σ) → Γ ⊢[ R^βιξη ]^nf σ
  reify^βιξη `Unit     T = `⟨⟩
  reify^βιξη `Bool     T = T
  reify^βιξη (σ `→ τ)  T = `λ $′ reify^βιξη τ $′ T (step refl) var‿0^βιξη
\end{code}

The semantic counterpart of \AIC{`ifte} can then be defined: if the boolean
is a value, the appropriate branch is picked; if it is stuck the whole expression
is reflected in the model.

\begin{code}
ifte^βιξη : {Γ : Con} {σ : ty} (b : Γ ⊨^βιξη `Bool) (l r : Γ ⊨^βιξη σ) → Γ ⊨^βιξη σ
ifte^βιξη `tt           l r = l
ifte^βιξη `ff           l r = r
ifte^βιξη (`embed _ T)  l r = reflect^βιξη _ $′ `ifte T (reify^βιξη _ l) (reify^βιξη _ r)
\end{code}

The \AF{Semantics} corresponding to Normalisation by Evaluation for βιξη-rules
uses \AF{\_⊨^{βιξη}\_} for values in the environment as well as the ones in the
model. The semantic counterpart of a λ-abstraction is simply the identity: the
structure of the functional case in the definition of the model matches precisely
the shape expected in a \AF{Semantics}. Because the environment carries model values,
the variable case is trivial.

\begin{code}
Normalise^βιξη : Semantics _⊨^βιξη_ _⊨^βιξη_
Normalise^βιξη = record
  { embed = λ σ → reflect^βιξη σ ∘ `var; wk = wk^βιξη _; ⟦var⟧ = id
  ; _⟦$⟧_ = _$^βιξη_; ⟦λ⟧ = id
  ; ⟦⟨⟩⟧ = ⟨⟩; ⟦tt⟧ = `tt; ⟦ff⟧ = `ff; ⟦ifte⟧  = ifte^βιξη }
\end{code}

The diagonal environment built up in \AF{Normalise^{βιξη}} \AF{⊨eval\_}
consists of η-expanded variables. Normalisation is obtained by reifying
the result of evaluation.

\begin{code}
norm^βιξη : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢[ R^βιξη ]^nf σ
norm^βιξη σ t = reify^βιξη σ $′ Normalise^βιξη ⊨eval t
\end{code}

\subsection{Normalisation by Evaluation for βιξ}

As we have just seen, the traditional typed model construction leads to a
normalisation procedure outputting βι-normal η-long terms. However evaluation
strategies implemented in actual proof systems tend to avoid applying η-rules
as much as possible: unsurprisingly, it is a rather bad idea to η-expand proof
terms which are already large when typechecking complex developments. Garillot
and colleagues~\cite{garillot2009packaging} report that common mathematical
structures packaged in records can lead to terms of such a size that theorem
proving becomes impractical.

In these systems, normal forms are neither η-long nor η-short: the η-rule is
actually never considered except when comparing two terms for equality, one of
which is neutral whilst the other is constructor-headed. Instead of declaring
them distinct, the algorithm will perform one step of η-expansion on the
neutral term and compare their subterms structurally. The conversion test
will only fail when confronted with two neutral terms with distinct head
variables or two normal forms with different head constructors.

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
R^βιξ : ty → Set
R^βιξ _ = ⊤

infix 5 _⊨^βιξ_ _⊨^βιξ⋆_
mutual
\end{code}}
\begin{code}
  _⊨^βιξ_   : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βιξ σ  = Γ ⊢[ R^βιξ ]^ne σ ⊎ Γ ⊨^βιξ⋆ σ

  _⊨^βιξ⋆_  : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βιξ⋆ `Unit     = ⊤
  Γ ⊨^βιξ⋆ `Bool     = Bool
  Γ ⊨^βιξ⋆ (σ `→ τ)  = {Δ : Con} → Γ ⊆ Δ → Δ ⊨^βιξ σ → Δ ⊨^βιξ τ
\end{code}

These mutual definitions allow us to make a careful distinction between values
arising from (non expanded) stuck terms and the ones wich are constructor headed
and have a computational behaviour associated to them. The values in the acting
model are storing these behaviours be it either actual proofs of \AF{⊤}, actual
\AF{Bool}eans or actual Agda functions depending on the type of the term. It is
important to note that the functions in the acting model have the model as both
domain and codomain: there is no reason to exclude the fact that both the argument
or the body may or may not be stuck.

Weakening for these structures is rather straightforward
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
reflect^βιξ : {Γ : Con} (σ : ty) (t : Γ ⊢[ R^βιξ ]^ne σ) → Γ ⊨^βιξ σ
reflect^βιξ σ = inj₁
\end{code}\vspace{-1.5em}
\AgdaHide{
\begin{code}
mutual
\end{code}}
\begin{code}
  reify^βιξ⋆ : {Γ : Con} (σ : ty) (T : Γ ⊨^βιξ⋆ σ) → Γ ⊢[ R^βιξ ]^nf σ
  reify^βιξ⋆ `Unit     T = `⟨⟩
  reify^βιξ⋆ `Bool     T = if T then `tt else `ff
  reify^βιξ⋆ (σ `→ τ)  T = `λ $′ reify^βιξ τ $′ T (step refl) var‿0^βιξ
    where var‿0^βιξ = inj₁ $ `var zero

  reify^βιξ : {Γ : Con} (σ : ty) (T : Γ ⊨^βιξ σ) → Γ ⊢[ R^βιξ ]^nf σ
  reify^βιξ σ (inj₁ ne)  = `embed _ ne
  reify^βιξ σ (inj₂ T)   = reify^βιξ⋆ σ T
\end{code}

Semantic application is slightly more interesting: we have to dispatch
depending on whether the function is a stuck term or not. In case it is,
we can reify its argument and grow the spine of the stuck term. Otherwise
we have an Agda function ready to be applied. We proceed similarly for
the definition of the semantical ``if then else''.

\AgdaHide{
\begin{code}
infixr 5 _$^βιξ_
\end{code}}
\begin{code}
_$^βιξ_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βιξ (σ `→ τ)) (u : Γ ⊨^βιξ σ) → Γ ⊨^βιξ τ
(inj₁ ne)  $^βιξ u = inj₁ $ ne `$ reify^βιξ _ u
(inj₂ F)   $^βιξ u = F refl u

ifte^βιξ : {Γ : Con} {σ : ty} (b : Γ ⊨^βιξ `Bool) (l r : Γ ⊨^βιξ σ) → Γ ⊨^βιξ σ
ifte^βιξ (inj₁ ne) l r = inj₁ $ `ifte ne (reify^βιξ _ l) (reify^βιξ _ r)
ifte^βιξ (inj₂ T)  l r = if T then l else r
\end{code}

Finally, we have all the necessary components to show that evaluating
the term whilst not η-expanding all stuck terms is a perfectly valid
\AR{Semantics}. As usual, normalisation is defined by composing
reification and evaluation on the diagonal environment.

\begin{code}
Normalise^βιξ : Semantics _⊨^βιξ_ _⊨^βιξ_
Normalise^βιξ = record
  { embed = λ σ → reflect^βιξ σ ∘ `var; wk = wk^βιξ; ⟦var⟧   = id
  ; _⟦$⟧_ = _$^βιξ_; ⟦λ⟧ = inj₂
  ; ⟦⟨⟩⟧ = inj₂ ⟨⟩; ⟦tt⟧ = inj₂ true; ⟦ff⟧ = inj₂ false; ⟦ifte⟧  = ifte^βιξ }
          
norm^βιξ : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢[ R^βιξ ]^nf σ
norm^βιξ σ t = reify^βιξ σ $′ Normalise^βιξ ⊨eval t
\end{code}

\subsection{Normalisation by Evaluation for βι}

The decision to lazily apply the η-rule can be pushed even further: one may
forgo using the ξ-rule too and simply perform weak-head normalisation. This
leads to pursuing the computation only when absolutely necessary e.g.
when two terms compared for equality have matching head constructors
and one needs to inspect these constructors' arguments to conclude. For
that purpose, we introduce an inductive family describing terms in weak-head
normal forms. Naturally, it is possible to define the corresponding weakenings
\AF{wk^{whne}} and \AF{wk^{whnf}} as well as erasure functions \AF{erase^{whnf}}
and \AF{erase^{whne}} with codomain \AD{\_⊢\_} (we omit their simple definitions here).

\AgdaHide{
\begin{code}
infix 5 _⊢^whne_ _⊢^whnf_
\end{code}}
\begin{code}
data _⊢^whne_ (Γ : Con) (σ : ty) : Set where
  `var   : (v : σ ∈ Γ) → Γ ⊢^whne σ
  _`$_   : {τ : ty} (t : Γ ⊢^whne (τ `→ σ)) (u : Γ ⊢ τ) → Γ ⊢^whne σ
  `ifte  : (b : Γ ⊢^whne `Bool) (l r : Γ ⊢ σ) → Γ ⊢^whne σ

data _⊢^whnf_ (Γ : Con) : (σ : ty) → Set where
  `embed   : {σ : ty} (t : Γ ⊢^whne σ) → Γ ⊢^whnf σ
  `⟨⟩      : Γ ⊢^whnf `Unit
  `tt `ff  : Γ ⊢^whnf `Bool
  `λ       : {σ τ : ty} (b : Γ ∙ σ ⊢ τ) → Γ ⊢^whnf (σ `→ τ)
\end{code}
\AgdaHide{
\begin{code}
wk^whne : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^whne σ) → Δ ⊢^whne σ
wk^whnf : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^whnf σ) → Δ ⊢^whnf σ
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
that source terms are now stored in the model too. This means that
from an element of the model, one can pick either the reduced version
of the original term (i.e. a stuck term or the term's computational
content) or the original term itself. We exploit this ability most
notably at reification time where once we have obtained either a
head constructor (respectively a head variable), none of the subterms
need to be evaluated.

\AgdaHide{
\begin{code}
mutual
\end{code}}
\begin{code}
  _⊨^βι_ : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βι σ  = Γ ⊢ σ  × (Γ ⊢^whne σ ⊎ Γ ⊨^βι⋆ σ)

  _⊨^βι⋆_ : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βι⋆ `Unit     = ⊤
  Γ ⊨^βι⋆ `Bool     = Bool
  Γ ⊨^βι⋆ (σ `→ τ)  = {Δ : Con} → Γ ⊆ Δ → Δ ⊨^βι σ → Δ ⊨^βι τ
\end{code}

\AgdaHide{
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

mutual

  reify^βι⋆ : {Γ : Con} (σ : ty) (T : Γ ⊨^βι⋆ σ) → Γ ⊢^whnf σ
  reify^βι⋆ `Unit     T = `⟨⟩
  reify^βι⋆ `Bool     T = if T then `tt else `ff
  reify^βι⋆ (σ `→ τ)  T = `λ $ proj₁ $ T (step refl) var‿0^βι
    where var‿0^βι = reflect^βι _ $ `var zero

  reify^βι : {Γ : Con} (σ : ty) (T : Γ ⊨^βι σ) → Γ ⊢^whnf σ
  reify^βι σ (t , inj₁ ne) = `embed ne
  reify^βι σ (t , inj₂ T)  = reify^βι⋆ σ T
\end{code}}

Weakening, reflection, and reification can all be defined rather
straightforwardly based on the template provided by the previous
section. The application and conditional branching rules are more
interesting: one important difference with respect to the previous
subsection is that we do not grow the spine of a stuck term using
reified versions of its arguments but rather the corresponding
\emph{source} term thus staying true to the idea that we only head
reduce enough to expose either a constructor or a variable.

\AgdaHide{
\begin{code}
infixr 5 _$^βι_
\end{code}}
\begin{code}
_$^βι_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βι σ `→ τ) (u : Γ ⊨^βι σ) → Γ ⊨^βι τ
(t , inj₁ ne)  $^βι (u , U) = t `$ u , inj₁ (ne `$ u)
(t , inj₂ T)   $^βι (u , U) = t `$ u , proj₂ (T refl (u , U))

ifte^βι : {Γ : Con} {σ : ty} (b : Γ ⊨^βι `Bool) (l r : Γ ⊨^βι σ) → Γ ⊨^βι σ
ifte^βι (b , inj₁ ne)  (l , L) (r , R) = `ifte b l r , inj₁ (`ifte ne l r)
ifte^βι (b , inj₂ B)   (l , L) (r , R) = `ifte b l r , (if B then L else R)
\end{code}

We can finally put together all of these semantic counterpart to
obtain a \AR{Semantics} corresponding to weak-head normalisation.
We omit the now self-evident definition of \AF{norm^{βι}} as the
composition of evaluation and reification.

\begin{code}
Normalise^βι : Semantics _⊨^βι_ _⊨^βι_
Normalise^βι = record
  { embed = λ σ → reflect^βι σ ∘ `var; wk = wk^βι; ⟦var⟧ = id
  ; _⟦$⟧_ = _$^βι_; ⟦λ⟧ = λ t → `λ (proj₁ $ t (step refl) (reflect^βι _ $ `var zero)) , inj₂ t
  ; ⟦⟨⟩⟧ = `⟨⟩ , inj₂ ⟨⟩; ⟦tt⟧ = `tt  , inj₂ true; ⟦ff⟧ = `ff  , inj₂ false; ⟦ifte⟧  = ifte^βι }
\end{code}
\AgdaHide{
\begin{code}
norm^βι : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^whnf σ
norm^βι σ t = reify^βι σ $′ Normalise^βι ⊨eval t
\end{code}}

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
However this does not entail that it is a meaningless exercise: the
result proven here will actually be useful in the following subsections
when considering more complex properties.

\subsection{The Synchronisation Relation}

This first example is basically describing the relational interpretation
of the terms. It should give the reader a good idea of the structure of
this type of setup before we move on to a more complex one. The types
involved might look a bit scary because of the level of generality that
we adopt but the idea is rather simple: two \AR{Semantics} are said to
be \emph{synchronisable} if, when evaluating a term in related environments,
they output related values. The bulk of the work is to make this intuition
formal.

The evidence that two \AR{Semantics} are \AR{Synchronisable} is
packaged in a record. The record is indexed by the two semantics
as well as two relations. The first relation (\AB{𝓔^R})
characterises the elements of the (respective) environment types
which are to be considered synchronised, and the second one (\AB{𝓜^R})
describes what synchronisation means in the model. We can lift
\AB{𝓔^R} in a pointwise manner to talk about entire environments
using the \AF{`∀[\_,\_]} predicate transformer omitted here.

\AgdaHide{
\begin{code}
`∀[_,_] :  {ℓ^A ℓ^B ℓ^R : Level} (𝓔^A : Con → ty → Set ℓ^A) (𝓔^B : Con → ty → Set ℓ^B)
           (𝓔^R : {Γ : Con} {σ : ty} (u^A : 𝓔^A Γ σ) (u^B : 𝓔^B Γ σ) → Set ℓ^R) →
           {Γ Δ : Con} (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Δ [ 𝓔^B ] Γ) → Set ℓ^R
`∀[ 𝓔^A , 𝓔^B ] 𝓔^R ρ^A ρ^B = (σ : ty) (pr : σ ∈ _) → 𝓔^R (ρ^A σ pr) (ρ^B σ pr)
\end{code}}
\begin{code}
record Synchronisable {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^RE ℓ^RM : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓜^A : (Γ : Con) (σ : ty) → Set ℓ^MA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓜^B : (Γ : Con) (σ : ty) → Set ℓ^MB} (𝓢^A : Semantics 𝓔^A 𝓜^A) (𝓢^B : Semantics 𝓔^B 𝓜^B)
  (𝓔^R  : {Γ : Con} {σ : ty} → 𝓔^A Γ σ → 𝓔^B Γ σ → Set ℓ^RE)
  (𝓜^R  : {Γ : Con} {σ : ty} → 𝓜^A Γ σ → 𝓜^B Γ σ → Set ℓ^RM) : Set (ℓ^RE ⊔ ℓ^RM ⊔ ℓ^EA ⊔ ℓ^EB ⊔ ℓ^MA ⊔ ℓ^MB) where
\end{code}
\AgdaHide{
\begin{code}
  module 𝓢^A = Semantics 𝓢^A
  module 𝓢^B = Semantics 𝓢^B
  field
\end{code}}

The record's fields are describing the structure these relations
need to have. \ARF{𝓔^R‿wk} states that two synchronised environments
can be weakened whilst staying synchronised.

\begin{code}
    𝓔^R‿wk  :  {Γ Δ Θ : Con} (inc : Δ ⊆ Θ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} (ρ^R : `∀[ 𝓔^A , 𝓔^B ] 𝓔^R {Γ} {Δ} ρ^A ρ^B) →
               `∀[ 𝓔^A , 𝓔^B ] 𝓔^R (wk[ 𝓢^A.wk ] inc ρ^A) (wk[ 𝓢^B.wk ] inc ρ^B)
\end{code}

We then have the relational counterparts of the term constructors.
To lighten the presentation, we will focus on the most interesting
ones and give only one example quite characteristic of the remaining
ones. Our first interesting case is the relational counterpart of
\AIC{`var}: it states that given two synchronised environments, we
indeed get synchronised values in the model by applying \ARF{⟦var⟧}
to the looked up values.

\begin{code}
    R⟦var⟧    :  {Γ Δ : Con} {σ : ty} (v : σ ∈ Γ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} (ρ^R : `∀[ 𝓔^A , 𝓔^B ] 𝓔^R ρ^A ρ^B) →
                 𝓜^R (𝓢^A.⟦var⟧ (ρ^A σ v)) (𝓢^B.⟦var⟧ (ρ^B σ v))
\end{code}

The second, and probably most interesting case, is the relational counterpart
to the \ARF{⟦λ⟧} combinator. The ability to evaluate the body of a \AIC{`λ} in
weakened environments, each extended by related values, and deliver synchronised
values is enough to guarantee that evaluating the lambdas in the original
environments will produce synchronised values.

\begin{code}
    R⟦λ⟧      :  {Γ : Con} {σ τ : ty} {f^A : {Δ : Con} → Γ ⊆ Δ → 𝓔^A Δ σ → 𝓜^A Δ τ} → {f^B : {Δ : Con} → Γ ⊆ Δ → 𝓔^B Δ σ → 𝓜^B Δ τ} → (f^r :  {Δ : Con} (inc : Γ ⊆ Δ) {u^A : 𝓔^A Δ σ} {u^B : 𝓔^B Δ σ} (u^R : 𝓔^R u^A u^B) → 𝓜^R  (f^A inc u^A) (f^B inc u^B)) →
                 𝓜^R (𝓢^A.⟦λ⟧ f^A) (𝓢^B.⟦λ⟧ f^B)
\end{code}

All the remaining cases are similar. We show here the relational
counterpart of the application constructor: it states that given
two induction hypotheses (and the knowledge that the two environment
used are synchronised), one can combine them to obtain a proof
about the evaluation of an application-headed term.

\begin{code}
    R⟦$⟧      :  {Γ : Con} {σ τ : ty} {f^A : 𝓜^A Γ $ σ `→ τ} {f^B : 𝓜^B Γ $ σ `→ τ} {u^A : 𝓜^A Γ σ} {u^B : 𝓜^B Γ σ} → 𝓜^R f^A f^B → 𝓜^R u^A u^B → 𝓜^R (f^A 𝓢^A.⟦$⟧ u^A) (f^B 𝓢^B.⟦$⟧ u^B)
\end{code}
\AgdaHide{
\begin{code}
    R⟦⟨⟩⟧     :  {Γ : Con} → 𝓜^R {Γ} 𝓢^A.⟦⟨⟩⟧ 𝓢^B.⟦⟨⟩⟧
    R⟦tt⟧     :  {Γ : Con} → 𝓜^R {Γ} 𝓢^A.⟦tt⟧ 𝓢^B.⟦tt⟧
    R⟦ff⟧     :  {Γ : Con} → 𝓜^R {Γ} 𝓢^A.⟦ff⟧ 𝓢^B.⟦ff⟧
    R⟦ifte⟧   :  {Γ : Con} {σ : ty} {b^A : _} {b^B : _} {l^A r^A : _} {l^B r^B : _} (b^R : 𝓜^R {Γ} {`Bool} b^A b^B)
                 (l^R : 𝓜^R l^A l^B) (r^R : 𝓜^R {Γ} {σ} r^A r^B) →
                 𝓜^R (𝓢^A.⟦ifte⟧ b^A l^A r^A) (𝓢^B.⟦ifte⟧ b^B l^B r^B)
infixl 10 [_,_,_]_∙^R_
\end{code}}

For this specification to be useful, we need to verify that we can indeed
benefit from its introduction. This is witnessed by two facts. First, our
ability to prove a fundamental lemma stating that given relations satisfying
this specification, the evaluation of a term in related environments yields
related values; second, our ability to find with various instances of such
synchronised semantics. Let us start with the fundamental lemma.

\paragraph{Fundamental Lemma of Synchronisable Semantics}
The fundamental lemma is indeed provable. We introduce a \AM{Synchronised}
module parametrised by a record packing the evidence that two semantics are
\AR{Synchronisable}. This allows us to bring all of the corresponding relational
counterpart of term constructors into scope by \AK{open}ing the record. The
traversal then uses them to combine the induction hypotheses arising structurally.
We use \AF{[\_,\_,\_]\_∙^R\_} as a way to circumvent Agda's inhability to
infer \AR{𝓔^A}, \AR{𝓔^B} and \AR{𝓔^R}.

\begin{code}
[_,_,_]_∙^R_ :  {ℓ^EA ℓ^EB ℓ^ER : Level} (𝓔^A : Con → ty → Set ℓ^EA) (𝓔^B : Con → ty → Set ℓ^EB)
                (𝓔^R : {Γ : Con} {σ : ty} → 𝓔^A Γ σ → 𝓔^B Γ σ → Set ℓ^ER)
                {Δ Γ : Con} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} {σ : ty} {u^A : 𝓔^A Δ σ} {u^B : 𝓔^B Δ σ} → `∀[ 𝓔^A , 𝓔^B ] 𝓔^R ρ^A ρ^B → 𝓔^R u^A u^B →
                `∀[ 𝓔^A , 𝓔^B ] 𝓔^R ([ 𝓔^A ] ρ^A `∙ u^A) ([ 𝓔^B ] ρ^B `∙ u^B)
[ 𝓔^A , 𝓔^B , 𝓔^R ] ρ^R ∙^R u^R = [ u^R , ρ^R ]

module Synchronised {ℓ^EA ℓ^MA ℓ^EB ℓ^MB : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓜^A : (Γ : Con) (σ : ty) → Set ℓ^MA} {𝓢^A : Semantics 𝓔^A 𝓜^A} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓜^B : (Γ : Con) (σ : ty) → Set ℓ^MB} {𝓢^B : Semantics 𝓔^B 𝓜^B} {ℓ^RE ℓ^RM : Level} {𝓔^R : {Γ : Con} {σ : ty} (u^A : 𝓔^A Γ σ) (u^B : 𝓔^B Γ σ) → Set ℓ^RE} {𝓜^R : {Γ : Con} {σ : ty} (mA : 𝓜^A Γ σ) (mB : 𝓜^B Γ σ) → Set ℓ^RM} (𝓡 : Synchronisable 𝓢^A 𝓢^B 𝓔^R 𝓜^R) where
  open Synchronisable 𝓡

  lemma :  {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} (ρ^R : `∀[ 𝓔^A , 𝓔^B ] 𝓔^R ρ^A ρ^B) →
           𝓜^R (𝓢^A ⊨⟦ t ⟧ ρ^A) (𝓢^B ⊨⟦ t ⟧ ρ^B)
  lemma (`var v)       ρ^R = R⟦var⟧ v ρ^R
  lemma (f `$ t)       ρ^R = R⟦$⟧ (lemma f ρ^R) (lemma t ρ^R)
  lemma (`λ t)         ρ^R = R⟦λ⟧ λ inc u^R → lemma t ([ 𝓔^A , 𝓔^B , 𝓔^R ] 𝓔^R‿wk inc ρ^R ∙^R u^R)
  lemma `⟨⟩            ρ^R = R⟦⟨⟩⟧
  lemma `tt            ρ^R = R⟦tt⟧
  lemma `ff            ρ^R = R⟦ff⟧
  lemma (`ifte b l r)  ρ^R = R⟦ifte⟧ (lemma b ρ^R) (lemma l ρ^R) (lemma r ρ^R)
\end{code}

\paragraph{Examples of Synchronisable Semantics}

Our first example of two synchronisable semantics is proving the
fact that \AF{Renaming} and \AF{Substitution} have precisely the
same behaviour whenever the environment we use for \AF{Substitution}
is only made up of variables. The (mundane) proofs which mostly
consist of using the congruence of propositional equality are
left out.

\begin{code}
SynchronisableRenamingSubstitution :  Synchronisable Renaming Substitution
                                      (λ v t → `var v ≡ t) _≡_
\end{code}
\AgdaHide{
\begin{code}
SynchronisableRenamingSubstitution =
  record
    { 𝓔^R‿wk  = λ inc ρ^R σ pr → PEq.cong (wk^⊢ inc) (ρ^R σ pr)
    ; R⟦var⟧    = λ v ρ^R → ρ^R _ v
    ; R⟦$⟧      = PEq.cong₂ _`$_
    ; R⟦λ⟧      = λ r → PEq.cong `λ (r (step refl) PEq.refl)
    ; R⟦⟨⟩⟧     = PEq.refl
    ; R⟦tt⟧     = PEq.refl
    ; R⟦ff⟧     = PEq.refl
    ; R⟦ifte⟧   = λ eqb eql → PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ eqb eql)
    }
\end{code}}

We show with the lemma \AF{RenamingIsASubstitution} how the result
we meant to prove is derived directly from the fundamental lemma of
\AR{Synchronisable} semantics:

\begin{code}
RenamingIsASubstitution : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Γ ⊆ Δ) →
  Renaming ⊨⟦ t ⟧ ρ ≡ Substitution ⊨⟦ t ⟧ (λ σ → `var ∘ ρ σ)
RenamingIsASubstitution t ρ = lemma t (λ σ pr → PEq.refl)
  where open Synchronised SynchronisableRenamingSubstitution
\end{code}


Another example of a synchronisable semantics is Normalisation by Evaluation
which can be synchronised with itself. This may appear like mindless symbol
pushing but it is actually crucial to prove such a theorem: we can only
define a Partial Equivalence Relation~\cite{mitchell1996foundations} (PER)
on the model used to implement Normalisation by Evaluation. The proofs of
the more complex properties of the procedure will rely heavily on the fact
that the exotic elements that may exist in the host language are actually
never produced by the evaluation function run on a term as long as all the
elements of the environment used were, themselves, not exotic i.e. equal to
themselves according to the PER.

We start with the definition of the PER for the model. It is constructed
by induction on the type and ensures that terms which behave the same
extensionally are declared equal. Two values of type \AIC{`Unit} are
always trivially equal;  values of type \AIC{`Bool} are normal forms
and are declared equal when they are effectively syntactically the same;
finally functions are equal whenever given equal inputs they yield equal
outputs.

\begin{code}
EQREL : (Γ : Con) (σ : ty) (T U : Γ ⊨^βιξη σ) → Set
EQREL Γ `Unit     T U = ⊤
EQREL Γ `Bool     T U = T ≡ U
EQREL Γ (σ `→ τ)  T U =  {Δ : Con} (inc : Γ ⊆ Δ) {V W : Δ ⊨^βιξη σ} (eqVW : EQREL Δ σ V W) →
                         EQREL Δ τ (T inc V) (U inc W)
\end{code}

It is indeed a PER as witnessed by the (omitted here) \AF{symEQREL} and
\AF{transEQREL} functions and it respects weakening as \AF{wk^{EQREL}} shows.

\begin{code}
symEQREL : {Γ : Con} (σ : ty) {S T : Γ ⊨^βιξη σ} → EQREL Γ σ S T → EQREL Γ σ T S
\end{code}
\AgdaHide{
\begin{code}
symEQREL `Unit     eq = ⟨⟩
symEQREL `Bool     eq = PEq.sym eq
symEQREL (σ `→ τ)  eq = λ inc eqVW → symEQREL τ (eq inc (symEQREL σ eqVW))
\end{code}}\vspace{-2.5em}%ugly but it works!
\begin{code}
transEQREL : {Γ : Con} (σ : ty) {S T U : Γ ⊨^βιξη σ} → EQREL Γ σ S T → EQREL Γ σ T U → EQREL Γ σ S U
\end{code}
\AgdaHide{
\begin{code}
  -- We are in PER so reflEQREL is not provable
  -- but as soon as EQREL σ V W then EQREL σ V V
reflEQREL : {Γ : Con} (σ : ty) {S T : Γ ⊨^βιξη σ} → EQREL Γ σ S T → EQREL Γ σ S S

transEQREL `Unit     eq₁ eq₂ = ⟨⟩
transEQREL `Bool     eq₁ eq₂ = PEq.trans eq₁ eq₂
transEQREL (σ `→ τ)  eq₁ eq₂ =
  λ inc eqVW → transEQREL τ (eq₁ inc (reflEQREL σ eqVW)) (eq₂ inc eqVW)

reflEQREL σ eq = transEQREL σ eq (symEQREL σ eq)
\end{code}}\vspace{-2.5em}%ugly but it works!
\begin{code}
wk^EQREL :  {Δ Γ : Con} (σ : ty) (inc : Γ ⊆ Δ) {T U : Γ ⊨^βιξη σ} → EQREL Γ σ T U → EQREL Δ σ (wk^βιξη σ inc T) (wk^βιξη σ inc U)
\end{code}
\AgdaHide{
\begin{code}
wk^EQREL `Unit     inc eq = ⟨⟩
wk^EQREL `Bool     inc eq = PEq.cong (wk^nf inc) eq
wk^EQREL (σ `→ τ)  inc eq = λ inc′ eqVW → eq (trans inc inc′) eqVW
\end{code}}

The interplay of reflect and reify with this notion of equality has
to be described in one go because of their being mutually defined.
It confirms our claim that \AF{EQREL} is indeed an appropriate notion
of semantic equality: values related by \AF{EQREL} are reified to
propositionally equal normal forms whilst propositionally equal neutral
terms are reflected to values related by \AF{EQREL}.

\begin{code}
reify^EQREL    :  {Γ : Con} (σ : ty) {T U : Γ ⊨^βιξη σ} → EQREL Γ σ T U → reify^βιξη σ T ≡ reify^βιξη σ U
reflect^EQREL  :  {Γ : Con} (σ : ty) {t u : Γ ⊢[ R^βιξη ]^ne σ} → t ≡ u → EQREL Γ σ (reflect^βιξη σ t) (reflect^βιξη σ u)
\end{code}
\AgdaHide{
\begin{code}
reify^EQREL `Unit     EQTU = PEq.refl
reify^EQREL `Bool     EQTU = EQTU
reify^EQREL (σ `→ τ)  EQTU = PEq.cong `λ $ reify^EQREL τ $ EQTU (step refl) $ reflect^EQREL σ PEq.refl

reflect^EQREL `Unit     eq = ⟨⟩
reflect^EQREL `Bool     eq = PEq.cong (`embed _) eq
reflect^EQREL (σ `→ τ)  eq = λ inc rel → reflect^EQREL τ $ PEq.cong₂ _`$_ (PEq.cong (wk^ne inc) eq) (reify^EQREL σ rel)

ifteRelNorm :
      let open Semantics Normalise^βιξη in
      {Γ : Con} {σ : ty} {b^A b^B : Γ ⊨^βιξη `Bool} {l^A l^B r^A r^B : Γ ⊨^βιξη σ} →
      EQREL Γ `Bool b^A b^B → EQREL Γ σ l^A l^B → EQREL Γ σ r^A r^B →
      EQREL Γ σ (⟦ifte⟧ b^A l^A r^A) (⟦ifte⟧ b^B l^B r^B)
ifteRelNorm {b^A = `tt}         PEq.refl l^R r^R = l^R
ifteRelNorm {b^A = `ff}         PEq.refl l^R r^R = r^R
ifteRelNorm {b^A = `embed _ ne} PEq.refl l^R r^R =
  reflect^EQREL _ (PEq.cong₂ (`ifte ne) (reify^EQREL _ l^R) (reify^EQREL _ r^R))
\end{code}}

And that's enough to prove that evaluating a term in two
environments related in a pointwise manner by \AF{EQREL}
yields two semantic objects themselves related by \AF{EQREL}.

\begin{code}
SynchronisableNormalise :  Synchronisable Normalise^βιξη Normalise^βιξη
                           (EQREL _ _) (EQREL _ _)
\end{code}
\AgdaHide{
\begin{code}
SynchronisableNormalise =
  record  { 𝓔^R‿wk  = λ inc ρ^R σ pr → wk^EQREL σ inc (ρ^R σ pr)
          ; R⟦var⟧   = λ v ρ^R → ρ^R _ v
          ; R⟦$⟧     = λ f → f refl
          ; R⟦λ⟧     = λ r → r
          ; R⟦⟨⟩⟧    = ⟨⟩
          ; R⟦tt⟧    = PEq.refl
          ; R⟦ff⟧    = PEq.refl
          ; R⟦ifte⟧  = ifteRelNorm
          }
\end{code}}

We omit the details of the easy proof but still recall the type
of the corollary of the fundamental lemma one obtains in this
case:

\begin{code}
refl^βιξη :  {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) {ρ^A ρ^B : Δ [ _⊨^βιξη_ ] Γ} (ρ^R : (σ : ty) (pr : σ ∈ Γ) → EQREL Δ σ (ρ^A σ pr) (ρ^B σ pr)) →
             EQREL Δ σ (Normalise^βιξη ⊨⟦ t ⟧ ρ^A) (Normalise^βιξη ⊨⟦ t ⟧ ρ^B)
refl^βιξη t ρ^R = lemma t ρ^R where open Synchronised SynchronisableNormalise
\end{code}


We can now move on to the more complex example of a proof
framework built generically over our notion of \AF{Semantics}

\subsection{Fusions of Evaluations}

When studying the meta-theory of a calculus, one systematically
needs to prove fusion lemmas for various semantics. For instance,
Benton et al.~\cite{benton2012strongly} prove six such lemmas
relating renaming, substitution and a typeful semantics embedding
their calculus into Coq. This observation naturally led us to
defining a fusion framework describing how to relate three semantics:
the pair we want to run sequentially and the third one they correspond
to. The fundamental lemma we prove can then be instantiated six times
to derive the corresponding corollaries.

The evidence that \AB{𝓢^A}, \AB{𝓢^B} and \AB{𝓢^C} are such
that \AB{𝓢^A} followed by \AB{𝓢^B} can be said to be equivalent
to \AB{𝓢^C} (e.g. think \AF{Substitution} followed by \AF{Renaming}
can be reduced to \AF{Substitution}) is packed in a record
\AR{Fusable} indexed by the three semantics but also three
relations. The first one (\AB{𝓔^R_{BC}}) states what it means
for two environment values of \AB{𝓢^B} and \AB{𝓢^C} respectively
to be related. The second one (\AB{𝓔^R}) characterises the triples
of environments (one for each one of the semantics) which are
compatible. Finally, the last one (\AB{𝓜^R}) relates values
in \AB{𝓢^B} and \AB{𝓢^C}'s respective models.

\begin{code}
record Fusable
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REBC ℓ^RM : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓔^C : (Γ : Con) (σ : ty) → Set ℓ^EC} {𝓜^A : (Γ : Con) (σ : ty) → Set ℓ^MA} {𝓜^B : (Γ : Con) (σ : ty) → Set ℓ^MB} {𝓜^C : (Γ : Con) (σ : ty) → Set ℓ^MC} (𝓢^A : Semantics 𝓔^A 𝓜^A) (𝓢^B : Semantics 𝓔^B 𝓜^B) (𝓢^C : Semantics 𝓔^C 𝓜^C)
  (𝓔^R‿BC : {Γ : Con} {σ : ty} (e^B : 𝓔^B Γ σ) (e^C : 𝓔^C Γ σ) → Set ℓ^REBC)
  (𝓔^R :  {Θ Δ Γ : Con} (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Θ [ 𝓔^B ] Δ) (ρ^C : Θ [ 𝓔^C ] Γ) → Set ℓ^RE)
  (𝓜^R : {Γ : Con} {σ : ty} (m^B : 𝓜^B Γ σ) (m^C : 𝓜^C Γ σ) → Set ℓ^RM)
  : Set (ℓ^RM ⊔ ℓ^RE ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA ⊔ ℓ^MA ⊔ ℓ^REBC) where
\end{code}
\AgdaHide{
\begin{code}
  module 𝓢^A = Semantics 𝓢^A
  module 𝓢^B = Semantics 𝓢^B
  module 𝓢^C = Semantics 𝓢^C
  field
\end{code}}

Similarly to the previous section, most of the fields of this
record describe what structure these relations need to have.
However, we start with something slightly different: given that
we are planing to run the \AR{Semantics} \AB{𝓢^B} \emph{after}
having run \AB{𝓢^A}, we need a way to extract a term from an
element of \AB{𝓢^A}'s model. Our first field is therefore
\ARF{reify^A}:

\begin{code}
    reify^A    : {Γ : Con} {σ : ty} (m : 𝓜^A Γ σ) → Γ ⊢ σ
\end{code}

Then come two constraints dealing with the relations talking
about evaluation environments. \ARF{𝓔^R‿∙} tells us how to
extend related environments: one should be able to push related
values onto the environments for \AB{𝓢^B} and \AB{𝓢^C} whilst
merely extending the one for \AB{𝓢^A} with a token value generated
using \ARF{embed}.

\ARF{𝓔^R‿wk} guarantees that it is always possible to weaken
the environments for \AB{𝓢^B} and \AB{𝓢^C} in a \AB{𝓔^R}
preserving manner.

\begin{code}
    𝓔^R‿∙   :  {Γ Δ Θ : Con} {σ : ty} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} {u^B : 𝓔^B Θ σ} {u^C : 𝓔^C Θ σ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) (u^R : 𝓔^R‿BC u^B u^C) →
               𝓔^R  ([ 𝓔^A ]  wk[ 𝓢^A.wk ] (step refl) ρ^A `∙ 𝓢^A.embed σ zero)
                    ([ 𝓔^B ]  ρ^B `∙ u^B) ([ 𝓔^C ]  ρ^C `∙ u^C)

    𝓔^R‿wk  :  {Γ Δ Θ E : Con} (inc : Θ ⊆ E) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
               𝓔^R ρ^A (wk[ 𝓢^B.wk ] inc ρ^B) (wk[ 𝓢^C.wk ] inc ρ^C)
\end{code}

Then we have the relational counterpart of the various term
constructors. As with the previous section, only a handful of
them are out of the ordinary. We will start with the \AIC{`var}
case. It states that fusion indeed happens when evaluating a
variable using related environments.

\begin{code}
    R⟦var⟧  :  {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
               𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A.⟦var⟧ (ρ^A σ v)) ⟧ ρ^B) (𝓢^C.⟦var⟧ (ρ^C σ v))
\end{code}

The \AIC{`λ}-case puts some rather strong restrictions on the way
the λ-abstraction's body may be used by \AB{𝓢^A}: we assume it
is evaluated in an environment weakened by one variable and extended
using \AB{𝓢^A}'s \ARF{embed}. But it is quite natural to have these
restrictions: given that \ARF{reify^A} quotes the result back, we are
expecting this type of evaluation in an extended context (i.e. under
one lambda). And it turns out that this is indeed enough for all of
our examples.
The evaluation environments used by the semantics \AB{𝓢^B} and \AB{𝓢^C}
on the other hand can be arbitrarily weakened before being extended with
related values to be substituted for the variable bound by the \AIC{`λ}.

\begin{code}
    R⟦λ⟧    :
      {Γ Δ Θ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
      (r :  {E : Con} (inc : Θ ⊆ E) {u^B : 𝓔^B E σ} {u^C : 𝓔^C E σ} (u^R : 𝓔^R‿BC u^B u^C) →
            let  ρ^A′ =  [ 𝓔^A ] wk[ 𝓢^A.wk ] (step refl) ρ^A `∙ 𝓢^A.embed σ zero
                 ρ^B′ =  [ 𝓔^B ] wk[ 𝓢^B.wk ] inc ρ^B `∙ u^B
                 ρ^C′ =  [ 𝓔^C ] wk[ 𝓢^C.wk ] inc ρ^C `∙ u^C
            in 𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ t ⟧ ρ^A′) ⟧ ρ^B′) (𝓢^C ⊨⟦ t ⟧ ρ^C′)) →
      𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ `λ t ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ `λ t ⟧ ρ^C)
\end{code}

The other cases are just a matter of stating that, given the
expected induction hypotheses, one can deliver a proof that
fusion can happen on the compound expression.

\AgdaHide{
\begin{code}
    R⟦$⟧    : {Γ Δ Θ : Con} {σ τ : ty} (f : Γ ⊢ σ `→ τ) (t : Γ ⊢ σ)
            {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} →
             (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ f ⟧ ρ^A) ⟧ ρ^B)
                   (𝓢^C ⊨⟦ f ⟧ ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ t ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ t ⟧ ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ f `$ t ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ f `$ t ⟧ ρ^C)

    R⟦⟨⟩⟧   : {Γ Δ Θ : Con} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} →
             (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ `⟨⟩ ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ `⟨⟩ ⟧ ρ^C)
    R⟦tt⟧   : {Γ Δ Θ : Con} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} →
             (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ `tt ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ `tt ⟧ ρ^C)
    R⟦ff⟧   : {Γ Δ Θ : Con} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} →
             (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ `ff ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ `ff ⟧ ρ^C)
    R⟦ifte⟧ : {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
            {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} →
             (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ b ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ b ⟧ ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ l ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ l ⟧ ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ r ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ r ⟧ ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ `ifte b l r ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ `ifte b l r ⟧ ρ^C)
\end{code}}

\paragraph{Fundamental Lemma of Fusable Semantics}

As with synchronisation, we measure the usefulness of this framework
by the fact that we can prove its fundamental lemma first and that
we get useful theorems out of it second. Once again, having carefully
identified what the constraints should be, proving the fundamental
lemma turns out to amount to a simple traversal we choose to omit here.

\begin{code}
module Fusion {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REB ℓ^RM : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓔^C : (Γ : Con) (σ : ty) → Set ℓ^EC} {𝓜^A : (Γ : Con) (σ : ty) → Set ℓ^MA} {𝓜^B : (Γ : Con) (σ : ty) → Set ℓ^MB} {𝓜^C : (Γ : Con) (σ : ty) → Set ℓ^MC} {𝓢^A : Semantics 𝓔^A 𝓜^A} {𝓢^B : Semantics 𝓔^B 𝓜^B} {𝓢^C : Semantics 𝓔^C 𝓜^C} {𝓔^R‿BC : {Γ : Con} {σ : ty} (e^B : 𝓔^B Γ σ) (e^C : 𝓔^C Γ σ) → Set ℓ^REB} {𝓔^R : {Θ Δ Γ : Con} (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Θ [ 𝓔^B ] Δ) (ρ^C : Θ [ 𝓔^C ] Γ) → Set ℓ^RE} {𝓜^R : {Γ : Con} {σ : ty} (mB : 𝓜^B Γ σ) (mC : 𝓜^C Γ σ) → Set ℓ^RM} (fusable : Fusable 𝓢^A 𝓢^B 𝓢^C 𝓔^R‿BC 𝓔^R 𝓜^R) where
  open Fusable fusable

  lemma :  {Γ Δ Θ : Con} {σ : ty} (t : Γ ⊢ σ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
           𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ t ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ t ⟧ ρ^C)
\end{code}
\AgdaHide{
\begin{code}
  lemma (`var v)       ρ^R = R⟦var⟧ v ρ^R
  lemma (f `$ t)       ρ^R = R⟦$⟧ f t ρ^R (lemma f ρ^R) (lemma t ρ^R)
  lemma (`λ t)         ρ^R = R⟦λ⟧ t ρ^R $ λ inc u^R → lemma t (𝓔^R‿∙ (𝓔^R‿wk inc ρ^R) u^R)
  lemma `⟨⟩            ρ^R = R⟦⟨⟩⟧ ρ^R
  lemma `tt            ρ^R = R⟦tt⟧ ρ^R
  lemma `ff            ρ^R = R⟦ff⟧ ρ^R
  lemma (`ifte b l r)  ρ^R = R⟦ifte⟧ b l r ρ^R (lemma b ρ^R) (lemma l ρ^R) (lemma r ρ^R)
\end{code}}

\paragraph{The Special Case of Syntactic Semantics}

Given that \AR{Syntactic} semantics use a lot of constructors
as their own semantic counterpart, it is possible to generate
evidence of them being fusable with much fewer assumptions.
We isolate them and prove the result generically in order to
avoid repeating ourselves.
A \AR{SyntacticFusable} record packs the evidence necessary to
prove that the \AR{Syntactic} semantics \AB{syn^A} and \AB{syn^B}
can be fused using the \AR{Syntactic} semantics \AB{syn^C}. It
is indexed by these three \AR{Syntactic}s as well as two relations
corresponding to the \AB{𝓔^R_{BC}} and \AB{𝓔^R} ones of the
\AR{Fusable} framework.

It contains the same \ARF{𝓔^R‿∙}, \ARF{𝓔^R‿wk} and \ARF{R⟦var⟧}
fields as a \AR{Fusable} as well as a fourth one (\ARF{embed^{BC}})
saying that \AB{syn^B} and \AB{syn^C}'s respective \ARF{embed}s are
producing related values.

\AgdaHide{
\begin{code}
record SyntacticFusable
  {ℓ^EA ℓ^EB ℓ^EC ℓ^REBC ℓ^RE : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓔^C : (Γ : Con) (σ : ty) → Set ℓ^EC} (synA : Syntactic 𝓔^A)
  (synB : Syntactic 𝓔^B)
  (synC : Syntactic 𝓔^C)
  (𝓔^R‿BC : {Γ : Con} {σ : ty} (e^B : 𝓔^B Γ σ) (e^C : 𝓔^C Γ σ) → Set ℓ^REBC)
  (𝓔^R : {Θ Δ Γ : Con} (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Θ [ 𝓔^B ] Δ) (ρ^C : Θ [ 𝓔^C ] Γ) → Set ℓ^RE)
  : Set (ℓ^RE ⊔ ℓ^REBC ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA)
  where
  module Syn^A = Syntactic synA
  module Syn^B = Syntactic synB
  module Syn^C = Syntactic synC
  field
    𝓔^R‿∙ : ({Γ Δ Θ : Con} {σ : ty} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ}
               {u^B : 𝓔^B Θ σ} {u^C : 𝓔^C Θ σ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) (u^R : 𝓔^R‿BC u^B u^C) →
               𝓔^R ([ 𝓔^A ] wk[ Syn^A.wk ] (step refl) ρ^A `∙ Syn^A.embed σ zero)
                      ([ 𝓔^B ] ρ^B `∙ u^B)
                      ([ 𝓔^C ] ρ^C `∙ u^C))
    𝓔^R‿wk : {Γ Δ Θ E : Con} (inc : Θ ⊆ E)
               {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
               𝓔^R ρ^A(wk[ Syn^B.wk ] inc ρ^B) (wk[ Syn^C.wk ] inc ρ^C)
    R⟦var⟧  : {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ}
              (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
              syntactic synB ⊨⟦ syntactic synA ⊨⟦ `var v ⟧ ρ^A ⟧ ρ^B ≡ syntactic synC ⊨⟦ `var v ⟧ ρ^C
\end{code}}
\begin{code}
    embed^BC : {Γ : Con} {σ : ty} → 𝓔^R‿BC  {Γ ∙ σ} (Syn^B.embed σ zero) (Syn^C.embed σ zero)
\end{code}

The important result is that given a \AR{SyntacticFusable} relating
three \AR{Syntactic} semantics, one can deliver a \AR{Fusable} relating
the corresponding \AR{Semantics} where \AB{𝓜^R} is the propositional
equality.

\begin{code}
syntacticFusable :  {ℓ^EA ℓ^EB ℓ^EC ℓ^RE ℓ^REBC : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓔^C : (Γ : Con) (σ : ty) → Set ℓ^EC} {syn^A : Syntactic 𝓔^A} {syn^B : Syntactic 𝓔^B} {syn^C : Syntactic 𝓔^C} {𝓔^R‿BC : {Γ : Con} {σ : ty} (e^B : 𝓔^B Γ σ) (e^C : 𝓔^C Γ σ) → Set ℓ^REBC} {𝓔^R : {Θ Δ Γ : Con} (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Θ [ 𝓔^B ] Δ) (ρ^C : Θ [ 𝓔^C ] Γ) → Set ℓ^RE} (syn^R : SyntacticFusable syn^A syn^B syn^C 𝓔^R‿BC 𝓔^R) →
  Fusable (syntactic syn^A) (syntactic syn^B) (syntactic syn^C) 𝓔^R‿BC 𝓔^R _≡_
\end{code}
\AgdaHide{
\begin{code}
syntacticFusable synF =
  let open SyntacticFusable synF in
  record
    { reify^A    = id
    ; 𝓔^R‿∙   = 𝓔^R‿∙
    ; 𝓔^R‿wk  = 𝓔^R‿wk
    ; R⟦var⟧    = R⟦var⟧
    ; R⟦$⟧      = λ f t ρ^R → PEq.cong₂ _`$_
    ; R⟦λ⟧      = λ t ρ^R r → PEq.cong `λ (r (step refl) embed^BC)
    ; R⟦⟨⟩⟧     = λ ρ^R → PEq.refl
    ; R⟦tt⟧     = λ ρ^R → PEq.refl
    ; R⟦ff⟧     = λ ρ^R → PEq.refl
    ; R⟦ifte⟧   = λ b l r ρ^R eqb eql → PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ eqb eql)
    }

`var-inj : {Γ : Con} {σ : ty} {pr₁ pr₂ : σ ∈ Γ} (eq : (Γ ⊢ σ ∋ `var pr₁) ≡ `var pr₂) → pr₁ ≡ pr₂
`var-inj PEq.refl = PEq.refl
\end{code}}

It is then trivial to prove that \AR{Renaming} can be fused with itself
to give rise to another renaming (obtained by composing the two context
inclusions): \ARF{𝓔^R‿∙} uses \AF{[\_,\_]}, a case-analysis combinator
for \AB{σ} \AD{∈} (\AB{Γ} \AIC{∙} τ) distinguishing the case where \AB{σ}
\AD{∈} \AB{Γ} and the one where \AB{σ} equals \AB{τ}, whilst the other connectives
are either simply combining induction hypotheses using the congruence of
propositional equality or even simply its reflexivity (the two \ARF{embed}s
we use are identical: they are both the one of \AF{syntacticRenaming} hence
why \ARF{embed^{BC}} is so simple).

\begin{code}
RenamingFusable :
  SyntacticFusable  syntacticRenaming syntacticRenaming syntacticRenaming
                    _≡_ (λ ρ^A ρ^B ρ^C → ∀ σ pr → ρ^B σ (ρ^A σ pr) ≡ ρ^C σ pr)
RenamingFusable = record
  { 𝓔^R‿∙     = λ ρ^R eq → [ eq , ρ^R ]
  ; 𝓔^R‿wk    = λ inc ρ^R σ pr → PEq.cong (inc σ) (ρ^R σ pr)
  ; R⟦var⟧    = λ v ρ^R → PEq.cong `var (ρ^R _ v)
  ; embed^BC  = PEq.refl }
\end{code}

Similarly, a \AR{Substitution} following a \AR{Renaming} is equivalent to
a \AR{Substitution} where the evaluation environment is the composition of
the two previous ones.

\begin{code}
RenamingSubstitutionFusable :
  SyntacticFusable syntacticRenaming syntacticSubstitution syntacticSubstitution
  _≡_ (λ ρ^A ρ^B ρ^C → ∀ σ pr → ρ^B σ (ρ^A σ pr) ≡ ρ^C σ pr)
\end{code}
\AgdaHide{
\begin{code}
RenamingSubstitutionFusable =
  record { 𝓔^R‿∙   = λ ρ^R eq → [ eq , ρ^R ]
         ; 𝓔^R‿wk  = λ inc ρ^R σ pr → PEq.cong (Renaming ⊨⟦_⟧ inc) (ρ^R σ pr)
         ; R⟦var⟧    = λ v ρ^R → ρ^R _ v
         ; embed^BC   = PEq.refl }
\end{code}}

Using the newly established fact about fusing two \AR{Renamings} together,
we can establish that a \AR{Substitution} followed by a \AR{Renaming} is
equivalent to a \AR{Substitution} where the elements in the evaluation
environment have been renamed.

\begin{code}
SubstitutionRenamingFusable :
  SyntacticFusable syntacticSubstitution syntacticRenaming syntacticSubstitution
  (λ v t → `var v ≡ t) (λ ρ^A ρ^B ρ^C → ∀ σ pr → Renaming ⊨⟦ ρ^A σ pr ⟧ ρ^B ≡ ρ^C σ pr)
\end{code}
\AgdaHide{
\begin{code}
SubstitutionRenamingFusable =
  let module RenRen = Fusion (syntacticFusable RenamingFusable) in
  record { 𝓔^R‿∙   = λ {_} {_} {_} {_} {ρ^A} {ρ^B} {ρ^C} ρ^R eq → [ eq , (λ σ pr →
                         PEq.trans (RenRen.lemma (ρ^A σ pr) (λ _ _ → PEq.refl))
                                   (ρ^R σ pr)) ]
         ; 𝓔^R‿wk  = λ inc {ρ^A} {ρ^B} {ρ^C} ρ^R σ pr →
                         PEq.trans (PEq.sym (RenRen.lemma (ρ^A σ pr) (λ _ _ → PEq.refl)))
                                   (PEq.cong (Renaming ⊨⟦_⟧ inc) (ρ^R σ pr))
         ; R⟦var⟧    = λ v ρ^R → ρ^R _ v
         ; embed^BC   = PEq.refl }
\end{code}}

Finally, using the fact that we now know how to fuse a \AR{Substitution}
and a \AR{Renaming} together no matter in which order they are performed,
we can prove that two \AR{Substitution}s can be fused together to give
rise to another \AR{Substitution}.

\begin{code}
SubstitutionFusable :
  SyntacticFusable syntacticSubstitution syntacticSubstitution syntacticSubstitution
  _≡_ (λ ρ^A ρ^B ρ^C → ∀ σ pr → Substitution ⊨⟦ ρ^A σ pr ⟧ ρ^B ≡ ρ^C σ pr)
\end{code}
\AgdaHide{
\begin{code}
SubstitutionFusable =
  let module RenSubst = Fusion (syntacticFusable RenamingSubstitutionFusable)
      module SubstRen = Fusion (syntacticFusable SubstitutionRenamingFusable) in
  record { 𝓔^R‿∙   = λ {_} {_} {_} {_} {ρ^A} {ρ^B} {ρ^C} ρ^R eq → [ eq , (λ σ pr →
                         PEq.trans (RenSubst.lemma (ρ^A σ pr) (λ _ _ → PEq.refl))
                                   (ρ^R σ pr)) ]
         ; 𝓔^R‿wk  = λ inc {ρ^A} {ρ^B} {ρ^C} ρ^R σ pr →
                         PEq.trans (PEq.sym (SubstRen.lemma (ρ^A σ pr) (λ _ _ → PEq.refl)))
                                   (PEq.cong (Renaming ⊨⟦_⟧ inc) (ρ^R σ pr))
         ; R⟦var⟧    = λ v ρ^R → ρ^R _ v
         ; embed^BC   = PEq.refl }

ifteRenNorm :
      {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
      {ρ^A : Δ [ flip _∈_ ] Γ} {ρ^B : Θ [ _⊨^βιξη_ ] Δ}
      {ρ^C : Θ [ _⊨^βιξη_ ] Γ} →
      (ρ^R : (σ : ty) (pr : σ ∈ Γ) → EQREL Θ σ (ρ^B σ (ρ^A σ pr)) (ρ^C σ pr)) →
      Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ b ⟧ ρ^A) ⟧ ρ^B ≡
      Normalise^βιξη ⊨⟦ b ⟧ ρ^C →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ l ⟧ ρ^A) ⟧ ρ^B)
      (Normalise^βιξη ⊨⟦ l ⟧ ρ^C) →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ r ⟧ ρ^A) ⟧ ρ^B)
      (Normalise^βιξη ⊨⟦ r ⟧ ρ^C) →
      EQREL Θ σ
      (Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ `ifte b l r ⟧ ρ^A) ⟧ ρ^B)
      (Normalise^βιξη ⊨⟦ `ifte b l r ⟧ ρ^C)
ifteRenNorm b l r {ρ^A} {ρ^B} {ρ^C} ρ^R eqb eql eqr
  with Normalise^βιξη ⊨⟦ Renaming ⊨⟦ b ⟧ ρ^A ⟧ ρ^B
     | Normalise^βιξη ⊨⟦ b ⟧ ρ^C
ifteRenNorm b l r ρ^R PEq.refl eql eqr | `embed _ t | `embed _ .t =
  reflect^EQREL _ (PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ PEq.refl (reify^EQREL _ eql)) (reify^EQREL _ eqr))
ifteRenNorm b l r ρ^R () eql eqr | `embed _ t | `tt
ifteRenNorm b l r ρ^R () eql eqr | `embed _ t | `ff
ifteRenNorm b l r ρ^R () eql eqr | `tt | `embed _ t
ifteRenNorm b l r ρ^R PEq.refl eql eqr | `tt | `tt = eql
ifteRenNorm b l r ρ^R () eql eqr | `tt | `ff
ifteRenNorm b l r ρ^R () eql eqr | `ff | `embed _ t
ifteRenNorm b l r ρ^R () eql eqr | `ff | `tt
ifteRenNorm b l r ρ^R PEq.refl eql eqr | `ff | `ff = eqr
\end{code}}

These four lemmas are usually painfully proven one after the other. Here
we managed to discharge them by simply instantiating our framework four
times in a row, using the former instances to discharge the constraints
arising in the later ones. But we are not at all limited to proving
statements about \AR{Syntactic}s only.

\paragraph{Examples of Fusable Semantics}

The most simple example of \AR{Fusable} \AR{Semantics} involving a non
\AR{Syntactic} one is probably the proof that \AR{Renaming} followed
by \AR{Normalise^{βιξη}} is equivalent to Normalisation by Evaluation
where the environment has been tweaked.

\begin{code}
RenamingNormaliseFusable : Fusable Renaming Normalise^βιξη Normalise^βιξη (EQREL _ _)
  (λ ρ^A ρ^B ρ^C → ∀ σ pr → EQREL _ σ (ρ^B σ (ρ^A σ pr)) (ρ^C σ pr)) (EQREL _ _)
\end{code}
\AgdaHide{
\begin{code}
RenamingNormaliseFusable =
  record
    { reify^A   = id
    ; 𝓔^R‿∙  = λ ρ^R u^R → [ u^R , ρ^R ]
    ; 𝓔^R‿wk = λ inc ρ^R → λ σ pr → wk^EQREL σ inc (ρ^R σ pr)
    ; R⟦var⟧   = λ v ρ^R → ρ^R _ v
    ; R⟦$⟧     = λ _ _ _ r → r refl
    ; R⟦λ⟧     = λ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ → ⟨⟩
    ; R⟦tt⟧    = λ _ → PEq.refl
    ; R⟦ff⟧    = λ _ → PEq.refl
    ; R⟦ifte⟧  = ifteRenNorm
    }


ifteSubstNorm :
     {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
      {ρ^A : Δ [ _⊢_ ] Γ} {ρ^B : Θ [ _⊨^βιξη_ ] Δ}
      {ρ^C : Θ [ _⊨^βιξη_ ] Γ} →
      ((σ₁ : ty) (pr : σ₁ ∈ Δ) → EQREL Θ σ₁ (ρ^B σ₁ pr) (ρ^B σ₁ pr)) ×
      ((σ₁ : ty) (pr : σ₁ ∈ Γ) {Θ₁ : Con} (inc : Θ ⊆ Θ₁) →
       EQREL Θ₁ σ₁
       (Normalise^βιξη ⊨⟦ ρ^A σ₁ pr ⟧
        (λ σ₂ pr₁ → wk^βιξη σ₂ inc $ ρ^B σ₂ pr₁))
       (wk^βιξη σ₁ inc $ ρ^C σ₁ pr))
      ×
      ((σ₁ : ty) (pr : σ₁ ∈ Γ) →
       EQREL Θ σ₁ (Normalise^βιξη ⊨⟦ ρ^A σ₁ pr ⟧ ρ^B) (ρ^C σ₁ pr)) →
      Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ b ⟧ ρ^A) ⟧ ρ^B ≡
      Normalise^βιξη ⊨⟦ b ⟧ ρ^C →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ l ⟧ ρ^A) ⟧ ρ^B)
      (Normalise^βιξη ⊨⟦ l ⟧ ρ^C) →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ r ⟧ ρ^A) ⟧ ρ^B)
      (Normalise^βιξη ⊨⟦ r ⟧ ρ^C) →
      EQREL Θ σ
      (Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ `ifte b l r ⟧ ρ^A) ⟧ ρ^B)
      (Normalise^βιξη ⊨⟦ `ifte b l r ⟧ ρ^C)
ifteSubstNorm b l r {ρ^A} {ρ^B} {ρ^C} ρ^R eqb eql eqr
  with Normalise^βιξη ⊨⟦ Substitution ⊨⟦ b ⟧ ρ^A ⟧ ρ^B
     | Normalise^βιξη ⊨⟦ b ⟧ ρ^C
ifteSubstNorm b l r ρ^R PEq.refl eql eqr | `embed _ t | `embed _ .t =
  reflect^EQREL _ (PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ PEq.refl (reify^EQREL _ eql)) (reify^EQREL _ eqr))
ifteSubstNorm b l r ρ^R () eql eqr | `embed _ t | `tt
ifteSubstNorm b l r ρ^R () eql eqr | `embed _ t | `ff
ifteSubstNorm b l r ρ^R () eql eqr | `tt | `embed _ t
ifteSubstNorm b l r ρ^R PEq.refl eql eqr | `tt | `tt = eql
ifteSubstNorm b l r ρ^R () eql eqr | `tt | `ff
ifteSubstNorm b l r ρ^R () eql eqr | `ff | `embed _ t
ifteSubstNorm b l r ρ^R () eql eqr | `ff | `tt
ifteSubstNorm b l r ρ^R PEq.refl eql eqr | `ff | `ff = eqr

wk-refl : {Γ : Con} (σ : ty) {T U : Γ ⊨^βιξη σ} →
          EQREL Γ σ T U → EQREL Γ σ (wk^βιξη σ refl T) U
wk-refl `Unit     eq = ⟨⟩
wk-refl `Bool     eq = PEq.trans (wk^nf-refl _) eq
wk-refl (σ `→ τ)  eq = eq

wk^2 : {Θ Δ Γ : Con} (σ : ty) (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ) {T U : Γ ⊨^βιξη σ} →
       EQREL Γ σ T U → EQREL Θ σ (wk^βιξη σ inc₂ $ wk^βιξη σ inc₁ T) (wk^βιξη σ (trans inc₁ inc₂) U)
wk^2 `Unit     inc₁ inc₂ eq = ⟨⟩
wk^2 `Bool     inc₁ inc₂ eq = PEq.trans (wk^nf-trans inc₁ inc₂ _) (PEq.cong (wk^nf (trans inc₁ inc₂)) eq)
wk^2 (σ `→ τ)  inc₁ inc₂ eq = λ inc₃ → eq (trans inc₁ $ trans inc₂ inc₃)
\end{code}}

Then, we use the framework to prove that to \AR{Normalise^{βιξη}} by
Evaluation after a \AR{Substitution} amounts to normalising the original
term where the substitution has been evaluated first. The constraints
imposed on the environments might seem quite restrictive but they are
actually similar to the Uniformity condition described by C. Coquand~\cite{coquand2002formalised}
in her detailed account of Normalisation by Evaluation for a simply-typed
λ-calculus with explicit substitution.


\begin{code}
SubstitutionNormaliseFusable : Fusable  Substitution Normalise^βιξη Normalise^βιξη
  (EQREL _ _)
  (λ ρ^A ρ^B ρ^C → `∀[ _⊨^βιξη_ , _⊨^βιξη_ ] (EQREL _ _ ) ρ^B ρ^B
                 × ((σ : ty) (pr : σ ∈ _) {Θ : Con} (inc : _ ⊆ Θ) →
                         EQREL Θ σ (Normalise^βιξη ⊨⟦ ρ^A σ pr ⟧ (λ σ pr → wk^βιξη σ inc $ ρ^B σ pr))
                                   (wk^βιξη σ inc $ ρ^C σ pr))
                 × ((σ : ty) (pr : σ ∈ _) → EQREL _ σ (Normalise^βιξη ⊨⟦ ρ^A σ pr ⟧ ρ^B) (ρ^C σ pr)))
  (EQREL _ _)
\end{code}
\AgdaHide{
\begin{code}
SubstitutionNormaliseFusable =
  let module RenNorm = Fusion RenamingNormaliseFusable
      module EqNorm  = Synchronised SynchronisableNormalise in
  record
    { reify^A   = id
    ; 𝓔^R‿∙  = λ {_} {_} {_} {_} {ρ^A} {ρ^B} {ρ^C} ρ^R u^R →
                     [ reflEQREL _ u^R , proj₁ ρ^R ]
                   , [ (λ {Θ} inc → wk^EQREL _ inc u^R)
                     , (λ σ pr {Θ} inc →
                       transEQREL σ (RenNorm.lemma (ρ^A σ pr)
                                                    (λ σ pr → wk^EQREL σ inc (proj₁ ρ^R σ pr)))
                                    ((proj₁ ∘ proj₂) ρ^R σ pr inc)) ]
                     , [ u^R , (λ σ pr → transEQREL σ (RenNorm.lemma (ρ^A σ pr) (proj₁ ρ^R))
                                          ((proj₂ ∘ proj₂) ρ^R σ pr)) ]
    ; 𝓔^R‿wk = λ inc {ρ^A} ρ^R →
                            (λ σ pr → wk^EQREL σ inc (proj₁ ρ^R σ pr))
                          , (λ σ pr {Θ} inc′ →
                               transEQREL σ (EqNorm.lemma (ρ^A σ pr)
                               (λ σ pr → transEQREL σ (wk^2 σ inc inc′ (proj₁ ρ^R σ pr))
                                                      (wk^EQREL σ (trans inc inc′) (proj₁ ρ^R σ pr))))
                               (transEQREL σ ((proj₁ ∘ proj₂) ρ^R σ pr (trans inc inc′))
                               (symEQREL σ (wk^2 σ inc inc′ (reflEQREL σ (symEQREL σ $ (proj₂ ∘ proj₂) ρ^R σ pr))))))
                          , (λ σ pr → (proj₁ ∘ proj₂) ρ^R σ pr inc)
    ; R⟦var⟧   = λ v ρ^R → (proj₂ ∘ proj₂) ρ^R _ v
    ; R⟦$⟧     = λ _ _ _ r → r refl
    ; R⟦λ⟧     = λ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ → ⟨⟩
    ; R⟦tt⟧    = λ _ → PEq.refl
    ; R⟦ff⟧    = λ _ → PEq.refl
    ; R⟦ifte⟧  = ifteSubstNorm
    }

both : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} (eq : (A × B ∋ a₁ , b₁) ≡ (a₂ , b₂)) → a₁ ≡ a₂ × b₁ ≡ b₂
both PEq.refl = PEq.refl , PEq.refl

∷-inj : {A : Set} {a b : A} {as bs : ∞ (Stream A)} (eq : (Stream A ∋ a ∷ as) ≡ b ∷ bs) → a ≡ b × as ≡ bs
∷-inj PEq.refl = PEq.refl , PEq.refl
\end{code}}

Finally, we may use the notion of \AR{Fusable} to prove that our
definition of pretty-printing ignores \AR{Renamings}. In other
words, as long as the names provided for the free variables are
compatible after the renaming and as long as the name supplies
are equal then the string produced, as well as the state of the
name supply at the end of the process, are equal.

\begin{code}
RenamingPrettyPrintingFusable : Fusable Renaming Printing Printing _≡_
  (λ ρ^A ρ^B → `∀[ Name , Name ] _≡_ (λ σ → ρ^B σ ∘ ρ^A σ))
  (λ p q → ∀ {names₁ names₂} → names₁ ≡ names₂ → runPrinter p names₁ ≡ runPrinter q names₂)
\end{code}
\AgdaHide{
\begin{code}
RenamingPrettyPrintingFusable = record
  { reify^A   = id
  ; 𝓔^R‿∙   = λ ρ^R eq → [ eq , ρ^R ]
  ; 𝓔^R‿wk  = λ _ ρ^R σ pr → PEq.cong (mkName ∘ runName) (ρ^R σ pr)
  ; R⟦var⟧   = λ v ρ^R → PEq.cong₂ (λ n ns → runName n , ns) (ρ^R _ v)
  ; R⟦λ⟧     = λ t ρ^R r → λ { {n₁ ∷ n₁s} {n₂ ∷ n₂s} eq →
                        let (neq   , nseq) = ∷-inj eq
                            (ihstr , ihns) = both (r (step refl) (PEq.cong mkName neq) (PEq.cong ♭ nseq))
                        in PEq.cong₂ _,_ (PEq.cong₂ (λ n str → "λ" ++ n ++ ". " ++ str) neq ihstr) ihns }
  ; R⟦$⟧     = λ f t {ρ^A} {ρ^B} {ρ^C} ρ^R ihf iht eq →
                        let (ihstrf , eq₁) = both (ihf eq)
                            (ihstrt , eq₂) = both (iht eq₁)
                        in PEq.cong₂ _,_ (PEq.cong₂ (λ strf strt → strf ++ " (" ++ strt ++ ")") ihstrf ihstrt) eq₂
  ; R⟦⟨⟩⟧    = λ _ → PEq.cong _
  ; R⟦tt⟧    = λ _ → PEq.cong _
  ; R⟦ff⟧    = λ _ → PEq.cong _
  ; R⟦ifte⟧  = λ b l r {ρ^A} {ρ^B} {ρ^C} ρ^R ihb ihl ihr eq →
                       let (ihstrb , eq₁) = both (ihb eq)
                           (ihstrl , eq₂) = both (ihl eq₁)
                           (ihstrr , eq₃) = both (ihr eq₂)
                       in PEq.cong₂ _,_ (PEq.cong₂ (λ strb strlr → "if (" ++ strb ++ ") then (" ++ strlr)
                                        ihstrb (PEq.cong₂ (λ strl strr → strl ++ ") else (" ++ strr ++ ")")
                                        ihstrl ihstrr)) eq₃ }

tailComm : (Δ Γ : Con) {names : Stream String} →
           tail (proj₂ (nameContext Δ Γ names)) ≡ proj₂ (nameContext Δ Γ (tail names))
tailComm Δ ε        = PEq.refl
tailComm Δ (Γ ∙ _)  = PEq.cong tail (tailComm Δ Γ)

proof : (Δ Γ : Con) {names : Stream String} → proj₂ (nameContext Δ Γ names) ≡ Stream.drop (size Γ) names
proof Δ ε       = PEq.refl
proof Δ (Γ ∙ _) = λ { {_ ∷ names} → PEq.trans (tailComm Δ Γ) (proof Δ Γ) }
\end{code}}
A direct corollary is that pretty printing a weakened closed term
amounts to pretty printing the term itself in a dummy environment.

\begin{code}
PrettyRenaming : {Γ : Con} {σ : ty} (t : ε ⊢ σ) (inc : ε ⊆ Γ) →
  print (wk^⊢ inc t) ≡ proj₁ (runPrinter (Printing ⊨⟦ t ⟧ (λ _ ())) $ Stream.drop (size Γ) names)
PrettyRenaming {Γ} t inc = PEq.cong proj₁ $ lemma t (λ _ ()) $ proof Γ Γ
  where open Fusion RenamingPrettyPrintingFusable
\end{code}

\section{Conclusion}

We have explained how to make using an inductive family to only represent
the terms of an eDSL which are well-scoped and well-typed by construction
more tractable. We proceeded by factoring out a common notion of \AR{Semantics}
encompassing a wide range of type and scope preserving traversals such as
renaming and substitution, which were already handled by the state of the
art~\cite{mcbride2005type,benton2012strongly}, but also pretty printing, or
various variations on normalisation by evaluation.
Our approach crucially relied on the careful distinction we made between
values in the environment and values in the model, as well as the slight
variation on the structure typical of Kripke-style models. Indeed, in our
formulation, the domain of a binder's interpretation is an environment
value rather than a model one.

We have then demonstrated that, having this shared structure, one could
further alleviate the implementer's pain by tackling the properties of
these \AR{Semantics} in a similarly abstract approach. We characterised,
using a first logical relation, the traversals which were producing
related outputs provided they were fed related inputs. A more involved
second logical relation gave us a general description of triples of
\AR{Fusable} semantics such that composing the two first ones would
yield an instance of the third one.

\newpage{}
\bibliography{main}

\end{document}
