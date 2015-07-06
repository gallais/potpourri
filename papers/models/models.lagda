%%%%% Pick one of the two
%\include{articleheader}
\include{sigplanheader}
%%%%
\usepackage{todonotes}
\include{commands}

\begin{document}
\title{Type-Preserving Semantics}
\maketitle{}

\begin{abstract}
Building on McBride's presentation of a subtitution algorithm for
the simply-typed lambda calculus implemented in terms of a single
type-and-scope-preserving traversal instantiated twice to define
renaming first and substitution later, we isolate a more general
notion of \AF{Semantics}.

Its careful distinction of environment and model values as well
as its Kripke structure make it generic enough to derive renaming
and substitution but also various variations on normalisation by
evaluation as well as, perhaps more surprisingly, a pretty-printing
function.
\end{abstract}

\section*{Introduction}

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

\paragraph{Formalisation} This paper is a literate Agda file slightly post-processed
to hide telescopes of implicit arguments and properly display (super / sub)-scripts.
This guarantees that all constructions are indeed well-typed, and all functions are
total. Nonetheless, it should be noted that the generic model constructions and the
various example of \AR{Semantics} given can be fully replicated in Haskell using GADTs
to describe both the terms themselves and the singletons~\cite{eisenberg2013dependently}
providing the user with the runtime descriptions of their types or their contexts'
shapes. The subtleties of working with dependent types in Haskell are outside the
scope of this paper but we do provide a (commented) Haskell development demonstrating
how to translate this article.

This yields, to the best of our knowledge, the first tagless and typeful implementation
of Normalization by Evaluation in Haskell. Danvy, Keller and Puech have achieved
a similar goal in OCaml~\cite{danvytagless} but their formalisation uses parametric
HOAS which frees them from having to deal with variable binding, contexts and use
Kripke structures in the model construction. However we consider these to be primordial
given that they can still guide the implementation of more complex type theories where,
until now, being typeful is still out of reach.


\AgdaHide{
\begin{code}
{-# OPTIONS --no-eta #-}
module models where

open import Level
open import Data.Unit
open import Data.Bool
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Function

infixr 1 _$′_
_$′_ : {A B : Set} (f : A → B) (a : A) → B
_$′_ = _$_
\end{code}}

\section{The Calculus}

We are going to illustrate these constructions using a definition of the
simply-typed λ-calculus which is well-scoped and well-typed by construction.
This presentation due to Altenkirch and Reus~\cite{altenkirch1999monadic}
relies heavily on Dybjer's inductive families~\cite{dybjer1991inductive}
and is carried out in Agda~\cite{norell2009dependently}.

We include \AIC{`Bool} and \AIC{`Unit} as base types as a minimal example of a
sum type and a record type equipped with an η-rule.

\AgdaHide{
\begin{code}
infixr 10 _`→_
\end{code}}
\begin{code}
data ty : Set where
  `Unit  : ty
  `Bool  : ty
  _`→_   : (σ τ : ty) → ty
\end{code}

In order to be able to build terms which are
well-scoped and well-typed by construction, we need a notion of contexts
(represented as snoc lists of types) and positions in them (represented as
typed de Bruijn indices~\cite{de1972lambda}).

\begin{code}
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

All the semantics we are interested in defining evaluate a term
written in the type-correct representation of the calculus defined
above given an interpretation of its free variable. We call the
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
_[_]_ :  {ℓ : Level} (Δ : Con) (R : (Δ : Con) (σ : ty) → Set ℓ)
         (Γ : Con) → Set ℓ
Δ [ R ] Γ = (σ : ty) (v : σ ∈ Γ) → R Δ σ
\end{code}

\AgdaHide{
\begin{code}
infixl 10 [_]_`∙_
\end{code}}

These environments can be built step by step by noticing that
the environment corresponding to an empty context is trivial
and that one may extend and already existing environment
provided a proof of the right type.

\begin{code}
`ε : {ℓ : Level} {Δ : Con} {R : (Δ : Con) (σ : ty) → Set ℓ} → Δ [ R ] ε
`ε = λ _ ()

[_]_`∙_ : {ℓ : Level} {Γ Δ : Con} (R : (Δ : Con) (σ : ty) → Set ℓ) {σ : ty}
          (ρ : Δ [ R ] Γ) (s : R Δ σ) → Δ [ R ] Γ ∙ σ
([ R ] ρ `∙ s) _ here!       = s
([ R ] ρ `∙ s) σ (there pr)  = ρ σ pr
\end{code}

\subsection{The Preoder of Context Inclusions}

One instance of environments one is accustomed to is the notion
of context inclusion. A context inclusion \AB{Γ} \AF{⊆} \AB{Δ}
is an environment pairing each variable of type \AB{σ} in \AB{Γ}
to one of the same type in \AB{Δ}.

\AgdaHide{
\begin{code}
infix 5 _⊆_
\end{code}}
\begin{code}
_⊆_ : (Γ Δ : Con) → Set
_⊆_ = flip _[ flip _∈_ ]_
\end{code}

Context inclusions allow for the formulation of weakening principles
explaining how to transport properties along inclusions: knowing that
\AB{P} holds of \AB{Γ} and that \AB{Γ} \AF{⊆} \AB{Δ} lets us conclude
that \AB{P} holds for \AB{Δ} too. In the case of variables, weakening
merely corresponds to applying the transport function in order to
obtain a renamed variable. The case of environments is also quite simple:
being a pointwise lifting of a relation \AB{R} between contexts and types,
they enjoy weakening if \AB{R} does.

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

pop! : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) → Γ ∙ σ ⊆ Δ ∙ σ
pop! inc σ here!       = here!
pop! inc σ (there pr)  = there $ inc σ pr

step : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) → Γ ⊆ Δ ∙ σ
step inc = trans inc $ λ _ → there
\end{code}

Now that we are equipped with the notion of inclusion, we have all
the pieces necessary to describe the Kripke structure of our models
of the simply-typed λ-calculus.

\section{Semantics and Generic Evaluation Function}

Because renaming, substitution, pretty-printing, and normalisation
by evaluation all share the same structure, we can abstract away a
notion of \AR{Semantics} encompassing all these constructions. This
makes it possible to implement a generic traversal parametrised by
such a \AR{Semantics} once and for all and gives us the opportunity
to focus on the interesting model constructions instead.

A \AR{Semantics} is indexed by two relations \AB{Env} and \AB{Mod}
describing respectively the values in the environment and the ones
in the model. It packs the properties of these relations necessary
to define the evaluation function.

Environment values need to come with a notion of weakening so that
the traversal may introduce variables (when going under a binder)
and keep the environment well-scoped. We also need to be able to
manufacture values in the environment given a variable in scope
in order to be able to craft a diagonal environment.

The structure of the model is quite constrained: each constructor
in the language needs a semantic counterpart. Most of them have a
type which is a direct translation of the type of the corresponding
constructor except for two interesting cases: \ARF{⟦var⟧} and \ARF{⟦λ⟧}.
The variable case guarantees that one can turn a value from the
environment into one in the model thus making it possible for the
traversal, when hitting a variable, to lookup the corresponding
value in the environment and return it. The semantic λ-abstraction
is notable for two reasons: following Mitchell and Moggi~\cite{mitchell1991kripke},
it has a Kripke structure thus allowing arbitrary extensions of the
context; and instead of being a function in the host language taking
values in the model as arguments, it takes environment values. This
slight variation in the type of the semantic λ-abstraction is what
makes it possible to go beyond the semantics such as substitution
or normalization by evaluation where \AB{Env} and \AB{Mod} happen
to coincide.

%\begin{figure*}
\begin{code}
record Semantics {ℓ^E ℓ^M : Level}
       (Env  : (Γ : Con) (σ : ty) → Set ℓ^E)
       (Mod  : (Γ : Con) (σ : ty) → Set ℓ^M) : Set (ℓ^E ⊔ ℓ^M) where
  infixl 5 _⟦$⟧_
  field
    wk      :  {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) (r : Env Γ σ) → Env Δ σ
    embed   :  {Γ : Con} (σ : ty) (pr : σ ∈ Γ) → Env Γ σ
    ⟦var⟧   :  {Γ : Con} {σ : ty} (v : Env Γ σ) → Mod Γ σ
    _⟦$⟧_   :  {Γ : Con} {σ τ : ty} → Mod Γ (σ `→ τ) → Mod Γ σ → Mod Γ τ
    ⟦λ⟧     :  {Γ : Con} {σ τ : ty} (t : {Δ : Con} (pr : Γ ⊆ Δ) (u : Env Δ σ) → Mod Δ τ) →
               Mod Γ (σ `→ τ)
    ⟦⟨⟩⟧    :  {Γ : Con} → Mod Γ `Unit
    ⟦tt⟧    :  {Γ : Con} → Mod Γ `Bool
    ⟦ff⟧    :  {Γ : Con} → Mod Γ `Bool
    ⟦ifte⟧  :  {Γ : Con} {σ : ty} (b : Mod Γ `Bool) (l r : Mod Γ σ) → Mod Γ σ
\end{code}
%\end{figure*}

The evaluation function is then defined by structural recursion on the
term by replacing each constructor with their semantic counterpart in
order to combine the induction hypotheses given by the subterms. In the
λ-abstraction case, the type of \ARF{⟦λ⟧} guarantees that the argument
can be stored in the environment which will have been weakened beforehand

one can build a diagonal environment for \AB{Γ} by \ARF{embed}ding its
variables.

\begin{code}
module Eval {ℓ^E ℓ^M : Level} {Env : (Γ : Con) (σ : ty) → Set ℓ^E} {Mod : (Γ : Con) (σ : ty) → Set ℓ^M} (Sem : Semantics Env Mod) where
  open Semantics Sem

  infix 10 _⊨⟦_⟧_ _⊨eval_
  eval : {Δ Γ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ Env ] Γ) → Mod Δ σ
  eval (`var v)       ρ = ⟦var⟧ $ ρ _ v
  eval (t `$ u)       ρ = eval t ρ ⟦$⟧ eval u ρ
  eval (`λ t)         ρ = ⟦λ⟧ λ inc u → eval t ([ Env ] wk[ wk ] inc ρ `∙ u)
  eval `⟨⟩            ρ = ⟦⟨⟩⟧
  eval `tt            ρ = ⟦tt⟧
  eval `ff            ρ = ⟦ff⟧
  eval (`ifte b l r)  ρ = ⟦ifte⟧ (eval b ρ) (eval l ρ) (eval r ρ)

  _⊨⟦_⟧_ : {Δ Γ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ Env ] Γ) → Mod Δ σ
  _⊨⟦_⟧_ = eval

  _⊨eval_ : {Γ : Con} {σ : ty} (t : Γ ⊢ σ) → Mod Γ σ
  _⊨eval_ t = _⊨⟦_⟧_ t embed

open Eval using (_⊨⟦_⟧_ ; _⊨eval_) public
\end{code}

\section{Syntactic Semantics}

This work being influenced by McBride's functional pearl~\cite{mcbride2005type},
it is only normal to start our exploration of \AR{Semantics} with the two
operations implemented with one single traversal. We call these operations
\AR{Syntactic} because the values in the model are actual terms and almost
all constructs are kept as their own semantic counterpart.

As observed by McBride, it is enough to provide three operations describing
the properties of the values in the environment to get a full-blown
\AR{Semantics}. This fact is witnessed by the \AF{syntactic} function.

\begin{code}
record Syntactic {ℓ : Level} (Env : (Γ : Con) (σ : ty) → Set ℓ) : Set ℓ where
  field
    embed  : {Γ : Con} (σ : ty) (pr : σ ∈ Γ) → Env Γ σ
    wk     : {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) → Env Γ σ → Env Δ σ
    ⟦var⟧  : {Γ : Con} {σ : ty} (v : Env Γ σ) → Γ ⊢ σ

syntactic : {ℓ : Level} {Env : (Γ : Con) (σ : ty) → Set ℓ} (syn : Syntactic Env) → Semantics Env _⊢_
syntactic syn =
  let open Syntactic syn in
  record  { wk      = wk
          ; embed   = embed
          ; ⟦var⟧   = ⟦var⟧
          ; _⟦$⟧_   = _`$_
          ; ⟦λ⟧     = λ t → `λ (t (step refl) (embed _ here!))
          ; ⟦⟨⟩⟧    = `⟨⟩
          ; ⟦tt⟧    = `tt
          ; ⟦ff⟧    = `ff
          ; ⟦ifte⟧  = `ifte
          }
\end{code}

\subsection{Functoriality, also known as Renaming}

Our first example of a \AR{Syntactic} works with variables as environment
values. As expected, we obtain a rather involved definition of the identity
function as \AF{Renaming} \AF{⊨eval\_}. But this construction is not at all
useless: indeed, the more general \AF{Renaming} \AF{⊨⟦\_⟧\_} function turns
out to be precisely the notion of weakening for terms we need.

\begin{code}
Renaming : Semantics (flip _∈_) _⊢_
Renaming = syntactic $
  record  { embed  = λ _ → id
          ; wk     = wk^∈
          ; ⟦var⟧  = `var }

wk^⊢ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) (t : Γ ⊢ σ) → Δ ⊢ σ
wk^⊢ = flip $ Renaming ⊨⟦_⟧_
\end{code}

\subsection{Parallel Substitution}

Our second example of a semantics is another spin on the syntactic model:
the environment values are now terms (but the diagonal environment obtained
by \ARF{embed}ding membership proofs will be made up of variables only).
Once more the semantic function \AF{Substitution} \AF{⊨⟦\_⟧\_} is more
interesting than the evaluation itself: it is an implementation of parallel
substitution.

\begin{code}
var‿0 : {Γ : Con} {σ : ty} → Γ ∙ σ ⊢ σ
var‿0 = `var here!

Substitution : Semantics _⊢_ _⊢_
Substitution = syntactic $
  record  { embed   = λ _ → `var
          ; wk      = wk^⊢ 
          ; ⟦var⟧   = id
          }

subst : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊢_ ] Γ) → Δ ⊢ σ
subst = Substitution ⊨⟦_⟧_
\end{code}

\section{Pretty Printing}

Before considering the various model constructions giving
rise to normalisation functions deciding different theories,
let us make a detour to a perhaps slightly more surprising
example of a \AF{Semantics}: pretty printing.

The distinction between the type of values in the environment and
the ones in the model is once more instrumental in giving the
procedure a precise type guiding our implementation. Indeed, the
environment carries \emph{names} for the variables currently in
scope whilst the inhabitants of the model are \emph{computations}
threading a stream to be used as a source of fresh names every
time a new variable is introduced by a \AIC{λ}-abstraction. If the
values in the environment were allowed to be computations too, we
would not root out all faulty implementations: the typechecker would
for instance quite happily accept a program picking a new name
every time a variable appears in the term.

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
                         return $ "if" ++ `b` ++ "then" ++ `l` ++ "else" ++ `r`
          }
  where
    deBruijn : {Γ : Con} {σ : ty} → σ ∈ Γ → ℕ
    deBruijn here!       = 0
    deBruijn (there pr)  = 1 + deBruijn pr
\end{code}

Our definition of \ARF{embed} erases the membership proofs to
recover the corresponding de Bruijn indices. This means that,
using \AF{PrettyPrinting} \AF{⊨eval\_}, the free variables will
be displayed as numbers whilst the bound ones will be given names.
Now, we still need to provide a \AD{Stream} of fresh names to
this computation in order to run it.

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
    
prettyPrint : {Γ : Con} {σ : ty} (t : Γ ⊢ σ) → String
prettyPrint t = proj₁ (PrettyPrinting ⊨eval t $ names)
\end{code}

\AgdaHide{
\begin{code}
pretty$ : {a b : ty} →
  let  app  :  ε ⊢ (a `→ b) `→ a `→ b
       app  =  `λ (`λ (`var (there here!) `$ `var here!))
  in prettyPrint app ≡ "λa. λb. a(b)"
pretty$ = PEq.refl
\end{code}}

\section{Recalling the four reduction rules}

Using \AF{Substitution}, we can implement \AF{beta}-reduction in
the usual manner.

\begin{code}
infixl 10 _⟨_/var₀⟩
_⟨_/var₀⟩ : {Γ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
t ⟨ u /var₀⟩ = subst t $ [ _⊢_ ] (λ _ → `var) `∙ u

beta : {Γ : Con} {σ τ : ty} (t : Γ ⊢ σ `→ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
beta (`λ b)  u = b ⟨ u /var₀⟩              -- β-reduction
beta t       u = t `$ u
\end{code}

\begin{code}
iota : {Γ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ) → Γ ⊢ σ
iota `tt  l _ = l                          -- ι-reduction
iota `ff  _ r = r                          -- ι-reduction
iota b    l r = `ifte b l r

eta : {Γ : Con} {σ τ : ty} (t : Γ ⊢ σ `→ τ) → Γ ⊢ σ `→ τ
eta t = `λ (wk^⊢ (step refl) t `$ var‿0)  -- η-expansion
\end{code}

%\begin{mathpar}
%\inferrule{
%  }{\text{(\AIC{`λ} \AB{t}) \AIC{`\$} \AB{u} ↝ \AB{t} \AF{⟨} \AB{u} \AF{/var₀⟩}}
%  }{β}
%\and
%\inferrule{\text{\AB{t} ↝ \AB{t′}}
%  }{\text{\AIC{`λ} \AB{t} ↝ \AIC{`λ} \AB{t′}}
%  }{ξ}
%\and
%\inferrule{
%  }{\text{\AB{t} ↝ \AF{eta} \AB{t}}
%  }{η}
%\end{mathpar}

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
Normalize^βξη : Semantics _⊨^βξη_ _⊨^βξη_
Normalize^βξη =
  record  { embed   = λ σ → reflect^βξη σ ∘ `var
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


Normalize^βξ : Semantics _⊨^βξ_ _⊨^βξ_
Normalize^βξ =
  record  { embed   = λ σ → reflect^βξ σ ∘ `var
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


Normalize^β : Semantics _⊨^β_ _⊨^β_
Normalize^β =
  record  { embed   = λ σ → reflect^β σ ∘ `var
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

\bibliography{main}

\end{document}
