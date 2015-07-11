%%%%% Pick one of the two
%\include{articleheader}
\include{sigplanheader}
%%%%
\usepackage{todonotes}
\usepackage{mathpartir}
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



\paragraph{Outline} We shall start by defining the simple calculus we will use
as a running example. We will then introduce a notion of environments which the
preorder of context inclusions is an example of. This will lead us to defining
a generic notion of type and scope-preserving \AR{Semantics} which can be used
to define a generic evaluation function. The rest of the paper is dedicated to
showcasing the ground covered by these \AR{Semantics}: from \AR{Syntactic} ones
corresponding to renaming and substitution to pretty-printing or some variations
on Normalisation by Evaluation.

\paragraph{Notations} This article is a literate Agda file typeset using the
\LaTeX{} backend with as little post-processing as possible: we simply hide
telescopes of implicit arguments and properly display (super / sub)-scripts
as well as special operators such as \AF{>>=} or \AF{++}. As such, a lot of
notations have a meaning in Agda: \AIC{green} identifiers are constructors,
\ARF{pink} names refer to record fields, and \AF{blue} is characteristic of
defined symbols. Underscores have a special status: when defining mixfix
identifiers~\cite{danielsson2011parsing}, they mark positions where arguments
may be inserted; our using the development version of Agda means that we have
access to Haskell-style sections i.e. one may write \AF{Renaming} \AF{⊨⟦\_⟧\_}
for the partial applications of \AF{\_⊨⟦\_⟧\_} to \AF{Renaming}.

\paragraph{Formalisation} This whole development being done in Agda guarantees that
all constructions are indeed well-typed, and all functions are total. Nonetheless,
it should be noted that the generic model constructions and the various example of
\AR{Semantics} given can be fully replicated in Haskell using GADTs to describe both
the terms themselves and the singletons~\cite{eisenberg2013dependently} providing the
user with the runtime descriptions of their types or their contexts' shapes. The
subtleties of working with dependent types in Haskell are outside the scope of this
paper but we do provide a (commented) Haskell module containing all the translated
definitions.

This yields, to the best of our knowledge, the first tagless and typeful implementation
of Normalisation by Evaluation in Haskell. Danvy, Keller and Puech have achieved
a similar goal in OCaml~\cite{danvytagless} but their formalisation uses parametric
HOAS which frees them from having to deal with variable binding, contexts and use
Kripke structures in the model construction. However we consider these to be primordial
given that they can still guide the implementation of more complex type theories where,
until now, being typeful is still out of reach but type-level guarantees about scope
preservation still helps to root out a lot of bugs.


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

[_]_`∙_ :  {ℓ : Level} {Γ Δ : Con} (R : (Δ : Con) (σ : ty) → Set ℓ) {σ : ty}
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
or normalisation by evaluation where \AB{Env} and \AB{Mod} happen
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
term. Each constructor is replaced by its semantic counterpart in order
to combine the induction hypotheses its subterms give rise to. In the
λ-abstraction case, the type of \ARF{⟦λ⟧} guarantees that the semantic
argument can be stored in the environment which will have been weakened
beforehand.

\begin{code}
module Eval {ℓ^E ℓ^M : Level} {Env : (Γ : Con) (σ : ty) → Set ℓ^E} {Mod : (Γ : Con) (σ : ty) → Set ℓ^M} (Sem : Semantics Env Mod) where
  open Semantics Sem

  infix 10 _⊨⟦_⟧_ _⊨eval_
  eval : {Δ Γ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ Env ] Γ) → Mod Δ σ
  eval (`var v)       ρ = ⟦var⟧ $ ρ _ v
  eval (t `$ u)       ρ = eval t ρ ⟦$⟧ eval u ρ
  eval (`λ t)         ρ = ⟦λ⟧  λ inc u →
                               eval t $ [ Env ] wk[ wk ] inc ρ `∙ u
  eval `⟨⟩            ρ = ⟦⟨⟩⟧
  eval `tt            ρ = ⟦tt⟧
  eval `ff            ρ = ⟦ff⟧
  eval (`ifte b l r)  ρ = ⟦ifte⟧ (eval b ρ) (eval l ρ) (eval r ρ)

  _⊨⟦_⟧_ : {Δ Γ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ Env ] Γ) → Mod Δ σ
  _⊨⟦_⟧_ = eval
\end{code}

One can build a diagonal environment for \AB{Γ} by \ARF{embed}ding its
variables. This gives us an \AF{\_⊨eval\_} function which will be used
to evaluate open terms. In the case of pretty-printing, this corresponds
to picking a naming scheme for free variables whilst in the usual model
construction used to perform normalisation by evaluation, it corresponds
to η-expanding the variables.

\begin{code}
  _⊨eval_ : {Γ : Con} {σ : ty} (t : Γ ⊢ σ) → Mod Γ σ
  _⊨eval_ t = _⊨⟦_⟧_ t embed
\end{code}

\AgdaHide{
\begin{code}
open Eval using (_⊨⟦_⟧_ ; _⊨eval_) public
\end{code}}

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
          ; ⟦λ⟧     = λ t → `λ $ t (step refl) $ embed _ here!
          ; ⟦⟨⟩⟧    = `⟨⟩
          ; ⟦tt⟧    = `tt
          ; ⟦ff⟧    = `ff
          ; ⟦ifte⟧  = `ifte
          }
\end{code}

One important mistake not to make is to think that this definition
performs some sort of η-expansion because of the definition of \ARF{⟦λ⟧}:
this operator is actually only ever used by \AF{\_⊨⟦\_⟧\_} when the
evaluated term is \emph{already} λ-headed so it is indeed perfectly
harmless.

We can now port McBride's definitions to our framework.

\subsection{Functoriality, also known as Renaming}

Our first example of a \AR{Syntactic} operation works with variables as
environment values. As expected, we obtain a rather involved definition of
the identity function as \AF{Renaming} \AF{⊨eval\_}. But this construction
is not at all useless: indeed, the more general \AF{Renaming} \AF{⊨⟦\_⟧\_}
function turns out to be precisely the notion of weakening for terms we need
once its arguments have been flipped.

\begin{code}
syntacticRenaming : Syntactic (flip _∈_)
syntacticRenaming =
  record  { embed  = λ _ → id
          ; wk     = wk^∈
          ; ⟦var⟧  = `var }

wk^⊢ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) (t : Γ ⊢ σ) → Δ ⊢ σ
wk^⊢ = flip $ syntactic syntacticRenaming ⊨⟦_⟧_
\end{code}
\AgdaHide{
\begin{code}
Renaming : Semantics (flip _∈_) _⊢_
Renaming = syntactic syntacticRenaming
\end{code}}

\subsection{Parallel Substitution}

Our second example of a semantics is another spin on the syntactic model:
the environment values are now terms (but the diagonal environment obtained
by \ARF{embed}ding membership proofs will be made up of variables only).
The \ARF{wk} operation now acts on terms and can only be defined because
\AF{Renaming} was implemented first.

Once more the semantic function \AF{Substitution} \AF{⊨⟦\_⟧\_} is more
interesting than the evaluation itself: it is an implementation of parallel
substitution.

\begin{code}
syntacticSubstitution : Syntactic _⊢_
syntacticSubstitution =
  record  { embed   = λ _ → `var
          ; wk      = wk^⊢ 
          ; ⟦var⟧   = id
          }

subst : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊢_ ] Γ) → Δ ⊢ σ
subst = syntactic syntacticSubstitution ⊨⟦_⟧_
\end{code}
\AgdaHide{
\begin{code}
Substitution : Semantics _⊢_ _⊢_
Substitution = syntactic syntacticSubstitution
\end{code}}

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
If the values in the environment were allowed to be computations too, we
would not root out all faulty implementations: the typechecker would for
instance quite happily accept a program picking a new name every time a
variable appears in the term.

Secondly, the fact that values in the model are computations and that this
poses no problem whatsoever in this framework means it is appropriate for
handling languages with effects~\cite{moggi1991notions}, or effectful
semantics (e.g. logging the various function calls).

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
                         return  $ "if (" ++ `b` ++ ") "
                                 ++ "then (" ++ `l` ++ ") "
                                 ++ "else (" ++ `r` ++ ")"
          }
  where
    deBruijn : {Γ : Con} {σ : ty} → σ ∈ Γ → ℕ
    deBruijn here!       = 0
    deBruijn (there pr)  = 1 + deBruijn pr
\end{code}

Our definition of \ARF{embed} erases the membership proofs to
recover the corresponding de Bruijn indices. This means that,
using \AF{PrettyPrinting} \AF{⊨eval\_}, the free variables will
be displayed as numbers whilst the bound ones will be given names
chosen by the name supply.

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

We can demonstrate that \AF{prettyPrint} does indeed do the job by
writing a test which is, given that type theory allows computation
at the type level, checked at typechecking time:

\begin{code}
pretty$ :  {a b : ty} → prettyPrint {Γ = ε} {σ = (a `→ b) `→ a `→ b} (`λ $ `λ $ `var (there here!) `$ `var here!)
           ≡ "λa. λb. a(b)"
pretty$ = PEq.refl
\end{code}

\section{Normalisation by Evaluation}

Normalisation by Evaluation is a technique leveraging the computational
power of a host language in order to normalise expressions of a deeply
embedded one. The process is based on a model construction associating
to each context \AB{Γ} and type \AB{σ}, a type of values \model{}. Two
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

\AgdaHide{
\begin{code}
infixl 10 _⟨_/var₀⟩
\end{code}}
\begin{code}
_⟨_/var₀⟩ : {Γ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
t ⟨ u /var₀⟩ = subst t $ [ _⊢_ ] (λ _ → `var) `∙ u
\end{code}

\begin{mathpar}
\inferrule{
  }{\text{(\AIC{`λ} \AB{t}) \AIC{`\$} \AB{u} ↝ \AB{t} \AF{⟨} \AB{u} \AF{/var₀⟩}}
  }{β}
\end{mathpar}

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

\begin{code}
eta : {Γ : Con} {σ τ : ty} (t : Γ ⊢ σ `→ τ) → Γ ⊢ σ `→ τ
eta t = `λ $ wk^⊢ (step refl) t `$ `var here!
\end{code}
\begin{mathpar}
\inferrule{
  }{\text{\AB{t} ↝ \AF{eta} \AB{t}}
  }{η_1}
\and
\inferrule{\text{\AB{t} \AgdaSymbol{:} \AB{Γ} \AD{⊢} \AIC{`Unit}}
  }{\text{\AB{t} ↝ \AIC{`⟨⟩}}
  }{η_2}
\end{mathpar}

Now that we have recalled all these rules, we can talk precisely
about the sort of equational theory decided by the model construction
we decide to perform. We start with the usual definition of Normalisation
by Evaluation which goes under λs and produces η-long βι-short normal
forms.

\subsection{Normalisation by Evaluation for βιξη}

These η-long βι-short normal forms can be formally described by two
mutually defined inductive families. Once more, context inclusions
induce a notion of weakening.

It should be noted that we do not enforce the fact that \AIC{`embed}
only lifts elment from the \AIC{`Bool} base type thus guaranteeing that
the η-rules have been applied as much as possible. This is purely for
brevety: we reuse this definition later on in a model definition where
no η-expansion is performed. If we were to add this extra constraint,
the programs in this subsection would stay exactly the same whilst
having a slightly more precise type.

\AgdaHide{
\begin{code}
infix 5 _⊢^ne_ _⊢^nf_
mutual
\end{code}}
\begin{code}
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

We now come to the definition of the model. It is such that we know that η-expansion
is applied eagerly: all inhabitants of \AB{Γ} \AF{⊨^βιξη} \AIC{`Unit} are indeed
equal and all elements of \AB{Γ} \AF{⊨^βιξη} \AB{σ} \AIC{`→} \AB{τ} are functions
in Agda meaning that their reifications will only ever be \AIC{`λ}-headed.

\AgdaHide{
\begin{code}
infix 5 _⊨^βιξη_
\end{code}}
\begin{code}
_⊨^βιξη_ : (Γ : Con) (σ : ty) → Set
Γ ⊨^βιξη `Unit   = ⊤
Γ ⊨^βιξη `Bool   = Γ ⊢^nf `Bool
Γ ⊨^βιξη σ `→ τ  = {Δ : Con} (inc : Γ ⊆ Δ) (u : Δ ⊨^βιξη σ) → Δ ⊨^βιξη τ

wk^βιξη : {Δ Γ : Con} (σ : ty) (inc : Γ ⊆ Δ) (T : Γ ⊨^βιξη σ) → Δ ⊨^βιξη σ
wk^βιξη `Unit     inc T = T
wk^βιξη `Bool     inc T = wk^nf inc T
wk^βιξη (σ `→ τ)  inc T = λ inc′ → T $′ trans inc inc′ 
\end{code}

The Kripke structure of the model makes it very simple to implement the
semantic counterpart of application.
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
the reflection and reification mechanisms first. Indeed we are going to need to be
able to reflect the stuck term into the model. The practical implication of this is
that a stuck \AIC{`ifte} will be effectively η-expanded.

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

ifte^βιξη : {Γ : Con} {σ : ty} (b : Γ ⊨^βιξη `Bool) (l r : Γ ⊨^βιξη σ) → Γ ⊨^βιξη σ
ifte^βιξη `tt         l r = l
ifte^βιξη `ff         l r = r
ifte^βιξη (`embed T)  l r = reflect^βιξη _ $′ `ifte T (reify^βιξη _ l) (reify^βιξη _ r)
\end{code}

The \AF{Semantics} corresponding to Normalisation by Evaluation for βιξη-rules
uses \AF{\_⊨^βιξη\_} for values in the environment as well as the ones in the
model. The semantic counterpart of a λ-abstraction is simply the identity: the
Kripke structure of the model matches precisely the one in \AF{Semantics}.
Because the environment carries model values, the variable case is as simple
as simply returning the value itself.

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

The diagonal environment built up in \AF{Normalise^βιξη} \AF{⊨eval\_} consists
of η-expanded variables. Normalisation is obtained by reifying the result
obtained by evaluation.

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
report that common mathematical structure packaged in records can lead to terms
of such a size that theorem proving becomes impractical.

In these systems, normal forms are neither η-long nor η-short: the η-rule is
actually never considered except when comparing two terms for equality, one of
which is neutral whilst the other is constructor-headed. Instead of declaring
them to be distinct, the algorithm will perform one step of η-expansion on the
neutral term and keep comparing their subterms structurally. The conversion test
will only fail when confronted with two neutral terms which have distinct head
variables or two normal forms with distinct head constructors.

It is possible to alter the model definition described earlier so that it
avoids unnecessary η-expansions. We proceed by enriching the traditional
model with extra syntactical artefacts in a manner reminiscent of Coquand
and Dybjer's approach to defining a Normalisation by Evaluation procedure
for the SK combinator calculus~\cite{CoqDybSK}. Their resorting to glueing
terms to elements of the model was dictated by the sheer impossibily to write
a sensible reification procedure but, in hindsight, it provides us with a
powerful technique to build models internalizing alternative equational
theories.


We mutually define the model and the \emph{acting} model which is the
computational part of the model. A value in the model is either a stuck
term or a value in the acting model which only contains canonical elements:
actual proofs of \AF{⊤}, actual \AF{Bool}eans and actual Agda functions
depending on the type. It is important to note that the functions in the
acting model have the model as both domain and codomain: there is no reason
to exclude the fact that both the argument and the body may or may not be
stuck.

\AgdaHide{
\begin{code}
infix 5 _⊨^βιξ_ _⊨^βιξ⋆_
\end{code}}
\begin{code}
mutual
  _⊨^βιξ_   : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βιξ σ  = Γ ⊢^ne σ
             ⊎ Γ ⊨^βιξ⋆ σ

  _⊨^βιξ⋆_  : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βιξ⋆ `Unit   = ⊤
  Γ ⊨^βιξ⋆ `Bool   = Bool
  Γ ⊨^βιξ⋆ σ `→ τ  = {Δ : Con} (inc : Γ ⊆ Δ) (u : Δ ⊨^βιξ σ) → Δ ⊨^βιξ τ
\end{code}

As expected the model enjoys weakening. Unsurprisingly what used to be
called reflection in the previous model is now trivial: stuck terms are
perfectly valid model values.

\begin{code}
wk^βιξ⋆ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (T : Γ ⊨^βιξ⋆ σ) → Δ ⊨^βιξ⋆ σ
wk^βιξ⋆ inc {`Unit   } T = T
wk^βιξ⋆ inc {`Bool   } T = T
wk^βιξ⋆ inc {σ `→ τ  } T = λ inc′ → T $′ trans inc inc′

wk^βιξ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) (T : Γ ⊨^βιξ σ) → Δ ⊨^βιξ σ
wk^βιξ inc (inj₁ ne)  = inj₁ $ wk^ne inc ne
wk^βιξ inc (inj₂ T)   = inj₂ $ wk^βιξ⋆ inc T

reflect^βιξ : {Γ : Con} (σ : ty) (t : Γ ⊢^ne σ) → Γ ⊨^βιξ σ
reflect^βιξ σ t = inj₁ t
\end{code}

Reification is quite straightforward too because no η-expansion is needed,
when encountering a stuck term, we simply embed it in the set of normal
forms.

\begin{code}
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
that. We proceed similarly for the definition of the semantical if then
else.

\AgdaHide{
\begin{code}
infixr 5 _$^βιξ_
\end{code}}
\begin{code}
_$^βιξ_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βιξ σ `→ τ) (u : Γ ⊨^βιξ σ) → Γ ⊨^βιξ τ
inj₁ ne  $^βιξ u = inj₁ $ ne `$ reify^βιξ _ u
inj₂ F   $^βιξ u = F refl u

ifte^βιξ : {Γ : Con} {σ : ty} (b : Γ ⊨^βιξ `Bool) (l r : Γ ⊨^βιξ σ) → Γ ⊨^βιξ σ
ifte^βιξ (inj₁ ne) l r = inj₁ $ `ifte ne (reify^βιξ _ l) (reify^βιξ _ r)
ifte^βιξ (inj₂ T)  l r = if T then l else r
\end{code}

Finally, we have all the components necessary to show that evaluating
the term whilst abstaining from η-expanding all stuck terms is a
perfectly valid \AR{Semantics}. As usual, normalisation is defined
by composition reification and evaluation on the diagonal environment.

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
forgo using the ξ-rule and simply perform weak-head normalisation, pursuing
the computation only when absolutely necessary e.g. when the two terms
compared for equality have matching head constructors and these constructors'
arguments need therefore to be inspected.

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

  infix 5 _⊨^βι_ _⊨^βι⋆_
  _⊨^βι_ : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βι σ  = Γ ⊢ σ ×  ( Γ ⊢^whne σ
                      ⊎ Γ ⊨^βι⋆ σ)

  _⊨^βι⋆_ : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βι⋆ `Unit   = ⊤
  Γ ⊨^βι⋆ `Bool   = Bool
  Γ ⊨^βι⋆ σ `→ τ  = {Δ : Con} (inc : Γ ⊆ Δ) (u : Δ ⊨^βι σ) → Δ ⊨^βι τ

wk^βι⋆ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (T : Γ ⊨^βι⋆ σ) → Δ ⊨^βι⋆ σ
wk^βι⋆ inc {`Unit   } T = T
wk^βι⋆ inc {`Bool   } T = T
wk^βι⋆ inc {σ `→ τ  } T = λ inc′ → T $′ trans inc inc′

wk^βι : {Δ Γ : Con}{σ : ty} (inc : Γ ⊆ Δ) (T : Γ ⊨^βι σ) → Δ ⊨^βι σ
wk^βι inc (t , inj₁ ne)  = wk^⊢ inc t , inj₁ (wk^whne inc ne)
wk^βι inc (t , inj₂ T)   = wk^⊢ inc t , inj₂ (wk^βι⋆ inc T)

reflect^βι : {Γ : Con} (σ : ty) (t : Γ ⊢^whne σ) → Γ ⊨^βι σ
reflect^βι σ t = erase^whne t , inj₁ t

var‿0^βι : {Γ : Con} {σ : ty} → Γ ∙ σ ⊨^βι σ
var‿0^βι = `var here! , inj₁ (`var here!)

source : {Γ : Con} {σ : ty} (T : Γ ⊨^βι σ) → Γ ⊢ σ
source (t , _) = t

mutual

  reify^βι⋆ : {Γ : Con} (σ : ty) (T : Γ ⊨^βι⋆ σ) → Γ ⊢^whnf σ
  reify^βι⋆ `Unit     T = `⟨⟩
  reify^βι⋆ `Bool     T = if T then `tt else `ff
  reify^βι⋆ (σ `→ τ)  T = `λ $′ proj₁ (T (step refl) var‿0^βι)

  reify^βι : {Γ : Con} (σ : ty) (T : Γ ⊨^βι σ) → Γ ⊢^whnf σ
  reify^βι σ (t , inj₁ ne) = `embed ne
  reify^βι σ (t , inj₂ T)  = reify^βι⋆ σ T

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
          ; ⟦λ⟧     = λ t → `λ (source (t (step refl) var‿0^βι)) , inj₂ t
          ; ⟦⟨⟩⟧    = `⟨⟩ , inj₂ tt
          ; ⟦tt⟧    = `tt , inj₂ true
          ; ⟦ff⟧    = `ff , inj₂ false
          ; ⟦ifte⟧  = ifte^βι
          }
          
norm^βι : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^whnf σ
norm^βι σ t = reify^βι σ $′ Normalise^βι ⊨eval t
\end{code}

\section{Semantics Properties}

Defining a wide variety of Semantics is all well and good but it
would be nice to be able to prove properties about them. Because
all of our semantics are implemented in the same fashion, it is
possible to design a generic framework to prove properties about
semantics.

\subsection{Synchronisation Relation}

Our first example of such a framework will stay simple on purpose.
However this does not mean that this is a meaningless exercise: the
lemmas proven here will actually be useful in the next subsection.

This first presentation should give the reader a good idea of the
organisation of this type of setup before we move on to a more
involved one. The types involved might look a bit scary because of
the level of generality that we adopt but the idea is rather simple:
Two \AR{Semantics} are said to be \emph{synchronisable} if, when
evaluating a term in related environments, they output related values.
The bulk of the work is to make this intuition formal.

The evidence that two \AR{Semantics} are \AR{Synchronisable} is
packaged in a record. The record is indexed by the semantics as
well as three relations. The first (\AB{RelEnvAB}) characterises
the elements of the (respective) environment types which are to
be considered equal, the second (\AB{RelEnv}) explains what it
means for two environements to be synchronised and the last
(\AB{RelMod}) describe synchronisation in the model.

\begin{code}
record Synchronisable
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB : Level} {EnvA : (Γ : Con) (σ : ty) → Set ℓ^EA} {ModA : (Γ : Con) (σ : ty) → Set ℓ^MA} (semA : Semantics EnvA ModA)
  {EnvB : (Γ : Con) (σ : ty) → Set ℓ^EB} {ModB : (Γ : Con) (σ : ty) → Set ℓ^MB} (semB : Semantics EnvB ModB)
  {ℓ^RE ℓ^RM ℓ^REAB : Level} (RelEnvAB : {Γ : Con} {σ : ty} (eA : EnvA Γ σ) (eB : EnvB Γ σ) → Set ℓ^REAB)
  (RelEnv : {Δ Γ : Con} (eA : Δ [ EnvA ] Γ) (eB : Δ [ EnvB ] Γ) → Set ℓ^RE)
  (RelMod : {Γ : Con} {σ : ty} (mA : ModA Γ σ) (mB : ModB Γ σ) → Set ℓ^RM)
  : Set (ℓ^RE ⊔ ℓ^RM ⊔ ℓ^EA ⊔ ℓ^EB ⊔ ℓ^MA ⊔ ℓ^MB ⊔ ℓ^REAB) where
\end{code}

The record's fields are describing the structure these relations
need to have. The first topic of interest is the interaction
between \AB{RelEnvAB} and \AB{RelEnv}. \ARF{RelEnv∙} states that
it should be possible to extend two synchronised environments as
long the elements we push onto them are themselves related by
\AB{RelEnvAB}. \ARF{RelEnvWk} states that two synchronised
environments can be weakened whilst staying synchronised.

\AgdaHide{
\begin{code}
  module SemA = Semantics semA
  module SemB = Semantics semB
  field
\end{code}}
\begin{code}
    RelEnv∙   :  {Γ Δ : Con} {σ : ty} {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ} {uA : EnvA Δ σ} {uB : EnvB Δ σ} (ρR : RelEnv ρA ρB) (uR : RelEnvAB uA uB) →
                 RelEnv ([ EnvA ] ρA `∙ uA) ([ EnvB ] ρB `∙ uB)
    RelEnvWk  :  {Γ Δ Θ : Con} (inc : Δ ⊆ Θ) {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ} (ρR : RelEnv ρA ρB) →
                 RelEnv  (wk[ SemA.wk ] inc ρA)
                         (wk[ SemB.wk ] inc ρB)
\end{code}

We then have the relational counterparts of the term constructors.
In order to lighten the presentation, we will only focus on the
interesting ones and give only one example of the ones which are
simply stating that the induction hypotheses can be combined in
a \AB{RelMod}-respecting manner.

The first interesting case is the relational counterpart of the
\AIC{`var} constructor: it states that given two synchronised
environments, we indeed get synchronised values in the model by
looking up the value associated to the same variable in both of
them.
\begin{code}
    R⟦var⟧    :  {Γ Δ : Con} {σ : ty} (v : σ ∈ Γ) {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ} (ρR : RelEnv ρA ρB) →
                 RelMod (semA ⊨⟦ `var v ⟧ ρA) (semB ⊨⟦ `var v ⟧ ρB)
\end{code}

The second, and probably most interesting case, is the description
of the relational counterpart of the \AIC{`λ}-abstraction which is
guided by the type of the \ARF{⟦λ⟧} combinator. It states that the
ability to evaluate the body of the λ in weakened environments each
extended by related values and deliver synchronised values in the
model is enough to guarantee that evaluating the lambdas in the original
environments will deliver synchronised values.

\begin{code}
    R⟦λ⟧      :  {Γ Δ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ} (ρR : RelEnv ρA ρB) →
                 (r :  {Θ : Con} (inc : Δ ⊆ Θ) {uA : EnvA Θ σ} {uB : EnvB Θ σ} (uR : RelEnvAB uA uB) →
                       let ρA′  = [ EnvA ] wk[ SemA.wk ] inc ρA `∙ uA
                           ρB′  = [ EnvB ] wk[ SemB.wk ] inc ρB `∙ uB
                       in RelMod  (semA ⊨⟦ t ⟧ ρA′) (semB ⊨⟦ t ⟧ ρB′)) →
                 RelMod (semA ⊨⟦ `λ t ⟧ ρA) (semB ⊨⟦ `λ t ⟧ ρB)
\end{code}

All the remaining cases are similar. We show here the relational
counterpart of the application constructor: it states that given
two induction hypotheses (and the knowledge that the two environment
used are synchronised), one can combine them to obtain a proof
about the evaluation of an application-headed term.

\begin{code}
    R⟦$⟧      :  {Γ Δ : Con} {σ τ : ty} (f : Γ ⊢ σ `→ τ) (t : Γ ⊢ σ) {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ} (ρR : RelEnv ρA ρB) →
                 RelMod (semA ⊨⟦ f ⟧ ρA) (semB ⊨⟦ f ⟧ ρB) → 
                 RelMod (semA ⊨⟦ t ⟧ ρA) (semB ⊨⟦ t ⟧ ρB) →
                 RelMod (semA ⊨⟦ f `$ t ⟧ ρA) (semB ⊨⟦ f `$ t ⟧ ρB)
\end{code}
\AgdaHide{
\begin{code}
    R⟦⟨⟩⟧     :  {Γ Δ : Con} {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ} (ρR : RelEnv ρA ρB) →
                 RelMod (semA ⊨⟦ `⟨⟩ ⟧ ρA) (semB ⊨⟦ `⟨⟩ ⟧ ρB)
    R⟦tt⟧     :  {Γ Δ : Con} {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ} (ρR : RelEnv ρA ρB) →
                 RelMod (semA ⊨⟦ `tt ⟧ ρA) (semB ⊨⟦ `tt ⟧ ρB)
    R⟦ff⟧     :  {Γ Δ : Con} {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ} (ρR : RelEnv ρA ρB) →
                 RelMod (semA ⊨⟦ `ff ⟧ ρA) (semB ⊨⟦ `ff ⟧ ρB)
    R⟦ifte⟧   :  {Γ Δ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ) {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ} (ρR : RelEnv ρA ρB) →
                 RelMod (semA ⊨⟦ b ⟧ ρA) (semB ⊨⟦ b ⟧ ρB) → 
                 RelMod (semA ⊨⟦ l ⟧ ρA) (semB ⊨⟦ l ⟧ ρB) →
                 RelMod (semA ⊨⟦ r ⟧ ρA) (semB ⊨⟦ r ⟧ ρB) →
                 RelMod (semA ⊨⟦ `ifte b l r ⟧ ρA) (semB ⊨⟦ `ifte b l r ⟧ ρB)
\end{code}}

What tells us that this specification is indeed the right one is, first,
our ability to prove the fundamental lemma corresponding to it and then
populate it with various instances of such synchronised semantics. Let
us start with the fundamental lemma.

The fundamental lemma is indeed provable as witnessed by the \AgdaModule{Synchronised}
module which is parametrised by a record of type \AR{Synchronizable} and
implements the \AF{synchronised} function which is omitted here because
it is a rather simple traversal inserting the term constructors' relational
counterparts in the right places.

\begin{code}
module Synchronised
\end{code}\vspace{-2em}%ugly but it works!
\AgdaHide{
\begin{code}
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB : Level}  {EnvA : (Γ : Con) (σ : ty) → Set ℓ^EA}  {ModA : (Γ : Con) (σ : ty) → Set ℓ^MA}  {semA : Semantics EnvA ModA}  {EnvB : (Γ : Con) (σ : ty) → Set ℓ^EB}  {ModB : (Γ : Con) (σ : ty) → Set ℓ^MB}  {semB : Semantics EnvB ModB}  {ℓ^RE ℓ^RM ℓ^REAB : Level}  {RelEnvAB : {Γ : Con} {σ : ty} (eA : EnvA Γ σ) (eB : EnvB Γ σ) → Set ℓ^REAB}  {RelEnv : {Δ Γ : Con} (eA : Δ [ EnvA ] Γ) (eB : Δ [ EnvB ] Γ) → Set ℓ^RE}  {RelMod : {Γ : Con} {σ : ty} (mA : ModA Γ σ) (mB : ModB Γ σ) → Set ℓ^RM}
\end{code}}
\begin{code}
  (rel : Synchronisable semA semB RelEnvAB RelEnv RelMod)
  where
\end{code}\vspace{-2em}%ugly but it works!
\AgdaHide{
\begin{code}
  open Synchronisable rel
\end{code}}
\begin{code}
  synchronised :  {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ} (ρR : RelEnv ρA ρB) →
                  RelMod (semA ⊨⟦ t ⟧ ρA) (semB ⊨⟦ t ⟧ ρB)
\end{code}
\AgdaHide{
\begin{code}
  synchronised (`var v)      ρR = R⟦var⟧ v ρR
  synchronised (f `$ t)      ρR = R⟦$⟧ f t ρR (synchronised f ρR) (synchronised t ρR)
  synchronised (`λ t)        ρR = R⟦λ⟧ t ρR $ λ inc uR → synchronised t (RelEnv∙ (RelEnvWk inc ρR) uR)
  synchronised `⟨⟩           ρR = R⟦⟨⟩⟧ ρR
  synchronised `tt           ρR = R⟦tt⟧ ρR
  synchronised `ff           ρR = R⟦ff⟧ ρR
  synchronised (`ifte b l r) ρR = R⟦ifte⟧ b l r ρR (synchronised b ρR) (synchronised l ρR) (synchronised r ρR)
\end{code}}

\subsubsection{Examples of Synchronisable Semantics}

Our first example of two synchronisable semantics is proving the
fact that \AF{Renaming} and \AF{Substitution} have precisely the
same behaviour whenever the environment we use for \AF{Substitution}
is only made up of variable. The (mundane) proofs are left out of
this article.

\begin{code}
SynchronisableRenamingSubstitution :
  Synchronisable Renaming Substitution
            (λ v t → `var v ≡ t)
            (λ ρA ρB → (σ : ty) (pr : σ ∈ _) → `var (ρA σ pr) ≡ ρB σ pr)
            _≡_
\end{code}
\AgdaHide{
\begin{code}
SynchronisableRenamingSubstitution =
  record
    { RelEnv∙   = λ ρR uR → [ uR , ρR ]
    ; RelEnvWk  = λ inc ρR σ pr → PEq.cong (wk^⊢ inc) (ρR σ pr)
    ; R⟦var⟧    = λ v ρR → ρR _ v
    ; R⟦$⟧      = λ _ _ _ → PEq.cong₂ _`$_
    ; R⟦λ⟧      = λ _  ρR r → PEq.cong `λ (r (step refl) PEq.refl)
    ; R⟦⟨⟩⟧     = λ _  → PEq.refl
    ; R⟦tt⟧     = λ _  → PEq.refl
    ; R⟦ff⟧     = λ _  → PEq.refl
    ; R⟦ifte⟧   = λ _ _ _ _ eqb eql → PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ eqb eql)
    }
\end{code}}

Another example of synchronisable semantics is normalisation by
evaluation which can be synchronised with itself. This may appear
like mindless symbol pushing but it is actually crucial to prove
such a theorem: the model is only a Partial Equivalence Relation~\cite{mitchell1996foundations}
(PER) and its properties will rely on the fact that the exotic
elements that may exist in the host language are never produced
by the evaluation function as long as all the elements of the
environment were, themselves, on the diagonal to begin with.

We start with the definition of the PER for the model:

\begin{code}
EQREL : (Γ : Con) (σ : ty) (T U : Γ ⊨^βιξη σ) → Set
EQREL Γ `Unit     T U = ⊤
EQREL Γ `Bool     T U = T ≡ U
EQREL Γ (σ `→ τ)  T U =
  {Δ : Con} (inc : Γ ⊆ Δ) {V W : Δ ⊨^βιξη σ} (eqVW : EQREL Δ σ V W) →
  EQREL Δ τ (T inc V) (U inc W)
\end{code}

It is indeed a PER as witnessed by \AF{symEQREL} and \AF{transEQREL}
(not shown here) and it respects weakening (\AF{wk^EQREL}).

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
    { RelEnv∙  = λ ρR uR → [ uR , ρR ]
    ; RelEnvWk = λ inc ρR σ pr → wk^EQREL σ inc (ρR σ pr)
    ; R⟦var⟧   = λ v ρR → ρR _ v
    ; R⟦$⟧     = λ _ _ _ f → f refl
    ; R⟦λ⟧     = λ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ → tt
    ; R⟦tt⟧    = λ _ → PEq.refl
    ; R⟦ff⟧    = λ _ → PEq.refl
    ; R⟦ifte⟧  = ifteRelNorm
    }
\end{code}}

\subsection{Fusions of Evaluations}

\begin{code}
record Fusable
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REBC ℓ^RM : Level}
  {EnvA   : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {EnvB   : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {EnvC   : (Γ : Con) (σ : ty) → Set ℓ^EC}
  {ModA   : (Γ : Con) (σ : ty) → Set ℓ^MA}
  {ModB   : (Γ : Con) (σ : ty) → Set ℓ^MB}
  {ModC   : (Γ : Con) (σ : ty) → Set ℓ^MC}
  (semA   : Semantics EnvA ModA)
  (semB   : Semantics EnvB ModB)
  (semC   : Semantics EnvC ModC)
  (RelEnvBC : {Γ : Con} {σ : ty} (eB : EnvB Γ σ) (eC : EnvC Γ σ) → Set ℓ^REBC)
  (RelEnv   : {Θ Δ Γ : Con} (eA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (eC : Θ [ EnvC ] Γ) → Set ℓ^RE)
  (RelMod   : {Γ : Con} {σ : ty} (mB : ModB Γ σ) (mC : ModC Γ σ) → Set ℓ^RM)
  : Set (ℓ^RM ⊔ ℓ^RE ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA ⊔ ℓ^MA ⊔ ℓ^REBC)
  where
  module SemA = Semantics semA
  module SemB = Semantics semB
  module SemC = Semantics semC
  field
    reifyA  : {Γ : Con} {σ : ty} (m : ModA Γ σ) → Γ ⊢ σ
    RelEnv∙ : ({Γ Δ Θ : Con} {σ : ty} {ρA : Δ [ EnvA ] Γ} {ρB : Θ [ EnvB ] Δ} {ρC : Θ [ EnvC ] Γ}
               {uB : EnvB Θ σ} {uC : EnvC Θ σ} (ρR : RelEnv ρA ρB ρC) (uR : RelEnvBC uB uC) →
               RelEnv ([ EnvA ] wk[ SemA.wk ] (step refl) ρA `∙ SemA.embed σ here!)
                      ([ EnvB ] ρB `∙ uB)
                      ([ EnvC ] ρC `∙ uC))
    RelEnvWk : {Γ Δ Θ E : Con} (inc : Θ ⊆ E)
               {ρA : Δ [ EnvA ] Γ} {ρB : Θ [ EnvB ] Δ} {ρC : Θ [ EnvC ] Γ} (ρR : RelEnv ρA ρB ρC) →
               RelEnv ρA (wk[ SemB.wk ] inc ρB) (wk[ SemC.wk ] inc ρC)
    R⟦var⟧  : {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ)
              (ρR : RelEnv ρA ρB ρC) →
              RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ `var v ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `var v ⟧ ρC)
    R⟦$⟧    : {Γ Δ Θ : Con} {σ τ : ty} (f : Γ ⊢ σ `→ τ) (t : Γ ⊢ σ)
            (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : RelEnv ρA ρB ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ f ⟧ ρA) ⟧ ρB) (semC ⊨⟦ f ⟧ ρC) → 
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ t ⟧ ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ f `$ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ f `$ t ⟧ ρC)
    R⟦λ⟧    : {Γ Δ Θ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ)
              (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) (ρR : RelEnv ρA ρB ρC) →
             (r : {E : Con} (inc : Θ ⊆ E) {uB : EnvB E σ} {uC : EnvC E σ} (uR : RelEnvBC uB uC) →
                  RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ t ⟧ ([ EnvA ] wk[ SemA.wk ] (step refl) ρA `∙ SemA.embed σ here!)) ⟧
                              ([ EnvB ] wk[ SemB.wk ] inc ρB `∙ uB))
                        (semC ⊨⟦ t ⟧ ([ EnvC ] wk[ SemC.wk ] inc ρC `∙ uC))) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ `λ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `λ t ⟧ ρC)
    R⟦⟨⟩⟧   : {Γ Δ Θ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : RelEnv ρA ρB ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ `⟨⟩ ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `⟨⟩ ⟧ ρC)
    R⟦tt⟧   : {Γ Δ Θ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : RelEnv ρA ρB ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ `tt ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `tt ⟧ ρC)
    R⟦ff⟧   : {Γ Δ Θ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : RelEnv ρA ρB ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ `ff ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `ff ⟧ ρC)
    R⟦ifte⟧ : {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
            (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : RelEnv ρA ρB ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ b ⟧ ρA) ⟧ ρB) (semC ⊨⟦ b ⟧ ρC) → 
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ l ⟧ ρA) ⟧ ρB) (semC ⊨⟦ l ⟧ ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ r ⟧ ρA) ⟧ ρB) (semC ⊨⟦ r ⟧ ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ `ifte b l r ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `ifte b l r ⟧ ρC)

module Fusion
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REB ℓ^RM : Level}
  {EnvA   : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {EnvB   : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {EnvC   : (Γ : Con) (σ : ty) → Set ℓ^EC}
  {ModA   : (Γ : Con) (σ : ty) → Set ℓ^MA}
  {ModB   : (Γ : Con) (σ : ty) → Set ℓ^MB}
  {ModC   : (Γ : Con) (σ : ty) → Set ℓ^MC}
  {semA   : Semantics EnvA ModA}
  {semB   : Semantics EnvB ModB}
  {semC   : Semantics EnvC ModC}
  {RelEnvBC : {Γ : Con} {σ : ty} (eB : EnvB Γ σ) (eC : EnvC Γ σ) → Set ℓ^REB}
  {RelEnv : {Θ Δ Γ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) → Set ℓ^RE}
  {RelMod : {Γ : Con} {σ : ty} (mB : ModB Γ σ) (mC : ModC Γ σ) → Set ℓ^RM}
  (fusable : Fusable semA semB semC RelEnvBC RelEnv RelMod)
  where
  open Fusable fusable
  
  fusion :
    {Γ Δ Θ : Con} {σ : ty}
    (t : Γ ⊢ σ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ)
             (ρR : RelEnv ρA ρB ρC) →
    RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ t ⟧ ρC)
  fusion (`var v)      ρA ρB ρC ρR = R⟦var⟧ v ρA ρB ρC ρR
  fusion (f `$ t)      ρA ρB ρC ρR = R⟦$⟧ f t ρA ρB ρC ρR (fusion f ρA ρB ρC ρR) (fusion t ρA ρB ρC ρR)
  fusion (`λ t)        ρA ρB ρC ρR = R⟦λ⟧ t ρA ρB ρC ρR $ λ inc uR →
                                     fusion t _ _ _ (RelEnv∙ (RelEnvWk inc ρR) uR)
  fusion `⟨⟩           ρA ρB ρC ρR = R⟦⟨⟩⟧ ρA ρB ρC ρR
  fusion `tt           ρA ρB ρC ρR = R⟦tt⟧ ρA ρB ρC ρR
  fusion `ff           ρA ρB ρC ρR = R⟦ff⟧ ρA ρB ρC ρR
  fusion (`ifte b l r) ρA ρB ρC ρR = R⟦ifte⟧ b l r ρA ρB ρC ρR ihb ihl ihr
    where ihb = fusion b ρA ρB ρC ρR
          ihl = fusion l ρA ρB ρC ρR
          ihr = fusion r ρA ρB ρC ρR

record SyntacticFusable
  {ℓ^EA ℓ^EB ℓ^EC ℓ^REBC ℓ^RE : Level}
  {EnvA  : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {EnvB  : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {EnvC  : (Γ : Con) (σ : ty) → Set ℓ^EC}
  (synA : Syntactic EnvA) (synB : Syntactic EnvB) (synC : Syntactic EnvC)
  (RelEnvBC : {Γ : Con} {σ : ty} (eB : EnvB Γ σ) (eC : EnvC Γ σ) → Set ℓ^REBC)
  (RelEnv : {Θ Δ Γ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) → Set ℓ^RE)
  : Set (ℓ^RE ⊔ ℓ^REBC ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA)
  where
  module SynA = Syntactic synA
  module SynB = Syntactic synB
  module SynC = Syntactic synC
  field
    RelEnv∙ : ({Γ Δ Θ : Con} {σ : ty} {ρA : Δ [ EnvA ] Γ} {ρB : Θ [ EnvB ] Δ} {ρC : Θ [ EnvC ] Γ}
               {uB : EnvB Θ σ} {uC : EnvC Θ σ} (ρR : RelEnv ρA ρB ρC) (uR : RelEnvBC uB uC) →
               RelEnv ([ EnvA ] wk[ SynA.wk ] (step refl) ρA `∙ SynA.embed σ here!)
                      ([ EnvB ] ρB `∙ uB)
                      ([ EnvC ] ρC `∙ uC))
    RelEnvWk : {Γ Δ Θ E : Con} (inc : Θ ⊆ E)
               {ρA : Δ [ EnvA ] Γ} {ρB : Θ [ EnvB ] Δ} {ρC : Θ [ EnvC ] Γ} (ρR : RelEnv ρA ρB ρC) →
               RelEnv ρA (wk[ SynB.wk ] inc ρB) (wk[ SynC.wk ] inc ρC)
    R⟦var⟧  : {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ)
              (ρR : RelEnv ρA ρB ρC) →
              syntactic synB ⊨⟦ syntactic synA ⊨⟦ `var v ⟧ ρA ⟧ ρB ≡ syntactic synC ⊨⟦ `var v ⟧ ρC
    embedBC : {Γ : Con} {σ : ty} → RelEnvBC {Γ ∙ σ} (SynB.embed σ here!) (SynC.embed σ here!)


syntacticFusable : 
  {ℓ^EA ℓ^EB ℓ^EC ℓ^RE ℓ^REBC : Level}
  {EnvA  : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {EnvB  : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {EnvC  : (Γ : Con) (σ : ty) → Set ℓ^EC}
  {synA : Syntactic EnvA} {synB : Syntactic EnvB} {synC : Syntactic EnvC}
  {RelEnvBC : {Γ : Con} {σ : ty} (eB : EnvB Γ σ) (eC : EnvC Γ σ) → Set ℓ^REBC}
  {RelEnv : {Θ Δ Γ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) → Set ℓ^RE}
  (synF : SyntacticFusable synA synB synC RelEnvBC RelEnv) →
   let open SyntacticFusable synF
   in Fusable (syntactic synA) (syntactic synB) (syntactic synC) RelEnvBC RelEnv _≡_
syntacticFusable synF =
  let open SyntacticFusable synF in
  record
    { reifyA    = id
    ; RelEnv∙   = RelEnv∙
    ; RelEnvWk  = RelEnvWk
    ; R⟦var⟧    = R⟦var⟧
    ; R⟦$⟧      = λ f t ρA ρB ρC ρR → PEq.cong₂ _`$_
    ; R⟦λ⟧      = λ t ρA ρB ρC ρR r → PEq.cong `λ (r (step refl) embedBC)
    ; R⟦⟨⟩⟧     = λ ρA ρB ρC ρR → PEq.refl
    ; R⟦tt⟧     = λ ρA ρB ρC ρR → PEq.refl
    ; R⟦ff⟧     = λ ρA ρB ρC ρR → PEq.refl
    ; R⟦ifte⟧   = λ b l r ρA ρB ρC ρR eqb eql → PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ eqb eql)
    }

`var-inj : {Γ : Con} {σ : ty} {pr₁ pr₂ : σ ∈ Γ} (eq : (Γ ⊢ σ ∋ `var pr₁) ≡ `var pr₂) → pr₁ ≡ pr₂
`var-inj PEq.refl = PEq.refl

RenamingFusable :
  SyntacticFusable syntacticRenaming syntacticRenaming syntacticRenaming
                   _≡_ (λ ρA ρB ρC → (σ : ty) (pr : σ ∈ _) → ρB σ (ρA σ pr) ≡ ρC σ pr)
RenamingFusable =
  record { RelEnv∙   = λ ρR eq → [ eq , ρR ]
         ; RelEnvWk  = λ inc ρR σ pr → PEq.cong (inc σ) (ρR σ pr)
         ; R⟦var⟧    = λ v _ _ _ ρR → PEq.cong `var (ρR _ v)
         ; embedBC   = PEq.refl }

RenamingSubstitutionFusable :
  SyntacticFusable syntacticRenaming syntacticSubstitution syntacticSubstitution
                   _≡_ (λ ρA ρB ρC → (σ : ty) (pr : σ ∈ _) → ρB σ (ρA σ pr) ≡ ρC σ pr)
RenamingSubstitutionFusable =
  record { RelEnv∙   = λ ρR eq → [ eq , ρR ]
         ; RelEnvWk  = λ inc ρR σ pr → PEq.cong (Renaming ⊨⟦_⟧ inc) (ρR σ pr)
         ; R⟦var⟧    = λ v _ _ _ ρR → ρR _ v
         ; embedBC   = PEq.refl }

SubstitutionRenamingFusable :
  SyntacticFusable syntacticSubstitution syntacticRenaming syntacticSubstitution
                   (λ v t → `var v ≡ t) (λ ρA ρB ρC → (σ : ty) (pr : σ ∈ _) → Renaming ⊨⟦ ρA σ pr ⟧ ρB ≡ ρC σ pr)
SubstitutionRenamingFusable =
  let module RenRen = Fusion (syntacticFusable RenamingFusable) in
  record { RelEnv∙   = λ {_} {_} {_} {_} {ρA} {ρB} {ρC} ρR eq → [ eq , (λ σ pr →
                         PEq.trans (RenRen.fusion (ρA σ pr) (step refl) _ ρB (λ _ _ → PEq.refl))
                                   (ρR σ pr)) ]
         ; RelEnvWk  = λ inc {ρA} {ρB} {ρC} ρR σ pr →
                         PEq.trans (PEq.sym (RenRen.fusion (ρA σ pr) ρB _ _ (λ _ _ → PEq.refl)))
                                   (PEq.cong (Renaming ⊨⟦_⟧ inc) (ρR σ pr))
         ; R⟦var⟧    = λ v _ _ _ ρR → ρR _ v
         ; embedBC   = PEq.refl }

SubstitutionFusable :
  SyntacticFusable syntacticSubstitution syntacticSubstitution syntacticSubstitution
                   _≡_ (λ ρA ρB ρC → (σ : ty) (pr : σ ∈ _) → Substitution ⊨⟦ ρA σ pr ⟧ ρB ≡ ρC σ pr)
SubstitutionFusable =
  let module RenSubst = Fusion (syntacticFusable RenamingSubstitutionFusable)
      module SubstRen = Fusion (syntacticFusable SubstitutionRenamingFusable) in
  record { RelEnv∙   = λ {_} {_} {_} {_} {ρA} {ρB} {ρC} ρR eq → [ eq , (λ σ pr →
                         PEq.trans (RenSubst.fusion (ρA σ pr) (step refl) _ ρB (λ _ _ → PEq.refl))
                                   (ρR σ pr)) ]
         ; RelEnvWk  = λ inc {ρA} {ρB} {ρC} ρR σ pr →
                         PEq.trans (PEq.sym (SubstRen.fusion (ρA σ pr) ρB _ _ (λ _ _ → PEq.refl)))
                                   (PEq.cong (Renaming ⊨⟦_⟧ inc) (ρR σ pr))
         ; R⟦var⟧    = λ v _ _ _ ρR → ρR _ v
         ; embedBC   = PEq.refl } 

ifteRenNorm :
      {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
      (ρA : Δ [ flip _∈_ ] Γ) (ρB : Θ [ _⊨^βιξη_ ] Δ)
      (ρC : Θ [ _⊨^βιξη_ ] Γ) →
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
ifteRenNorm b l r ρA ρB ρC ρR eqb eql eqr
  with Normalise^βιξη ⊨⟦ Renaming ⊨⟦ b ⟧ ρA ⟧ ρB
     | Normalise^βιξη ⊨⟦ b ⟧ ρC
ifteRenNorm b l r ρA ρB ρC ρR PEq.refl eql eqr | `embed t | `embed .t =
  reflect^EQREL _ (PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ PEq.refl (reify^EQREL _ eql)) (reify^EQREL _ eqr))
ifteRenNorm b l r ρA ρB ρC ρR () eql eqr | `embed t | `tt
ifteRenNorm b l r ρA ρB ρC ρR () eql eqr | `embed t | `ff
ifteRenNorm b l r ρA ρB ρC ρR () eql eqr | `tt | `embed t
ifteRenNorm b l r ρA ρB ρC ρR PEq.refl eql eqr | `tt | `tt = eql
ifteRenNorm b l r ρA ρB ρC ρR () eql eqr | `tt | `ff
ifteRenNorm b l r ρA ρB ρC ρR () eql eqr | `ff | `embed t
ifteRenNorm b l r ρA ρB ρC ρR () eql eqr | `ff | `tt
ifteRenNorm b l r ρA ρB ρC ρR PEq.refl eql eqr | `ff | `ff = eqr

RenamingNormaliseFusable :
  Fusable Renaming Normalise^βιξη Normalise^βιξη
          (EQREL _ _) (λ ρA ρB ρC → (σ : ty) (pr : σ ∈ _) → EQREL _ σ (ρB σ (ρA σ pr)) (ρC σ pr))
          (EQREL _ _)
RenamingNormaliseFusable =
  record
    { reifyA   = id
    ; RelEnv∙  = λ ρR uR → [ uR , ρR ]
    ; RelEnvWk = λ inc ρR → λ σ pr → wk^EQREL σ inc (ρR σ pr)
    ; R⟦var⟧   = λ v _ _ _ ρR → ρR _ v
    ; R⟦$⟧     = λ _ _ _ _ _ _ r → r refl
    ; R⟦λ⟧     = λ _ _ _ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ _ _ _ → tt
    ; R⟦tt⟧    = λ _ _ _ _ → PEq.refl
    ; R⟦ff⟧    = λ _ _ _ _ → PEq.refl
    ; R⟦ifte⟧  = ifteRenNorm
    }


ifteSubstNorm :
     {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
      (ρA : Δ [ _⊢_ ] Γ) (ρB : Θ [ _⊨^βιξη_ ] Δ)
      (ρC : Θ [ _⊨^βιξη_ ] Γ) →
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
ifteSubstNorm b l r ρA ρB ρC ρR eqb eql eqr
  with Normalise^βιξη ⊨⟦ Substitution ⊨⟦ b ⟧ ρA ⟧ ρB
     | Normalise^βιξη ⊨⟦ b ⟧ ρC
ifteSubstNorm b l r ρA ρB ρC ρR PEq.refl eql eqr | `embed t | `embed .t =
  reflect^EQREL _ (PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ PEq.refl (reify^EQREL _ eql)) (reify^EQREL _ eqr))
ifteSubstNorm b l r ρA ρB ρC ρR () eql eqr | `embed t | `tt
ifteSubstNorm b l r ρA ρB ρC ρR () eql eqr | `embed t | `ff
ifteSubstNorm b l r ρA ρB ρC ρR () eql eqr | `tt | `embed t
ifteSubstNorm b l r ρA ρB ρC ρR PEq.refl eql eqr | `tt | `tt = eql
ifteSubstNorm b l r ρA ρB ρC ρR () eql eqr | `tt | `ff
ifteSubstNorm b l r ρA ρB ρC ρR () eql eqr | `ff | `embed t
ifteSubstNorm b l r ρA ρB ρC ρR () eql eqr | `ff | `tt
ifteSubstNorm b l r ρA ρB ρC ρR PEq.refl eql eqr | `ff | `ff = eqr

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
 

SubstitutionNormaliseFusable :
  Fusable Substitution Normalise^βιξη Normalise^βιξη
          (EQREL _ _)
          (λ ρA ρB ρC → ((σ : ty) (pr : σ ∈ _) → EQREL _ σ (ρB σ pr) (ρB σ pr))
                      × ((σ : ty) (pr : σ ∈ _) {Θ : Con} (inc : _ ⊆ Θ) →
                         EQREL Θ σ (Normalise^βιξη ⊨⟦ ρA σ pr ⟧ (λ σ pr → wk^βιξη σ inc $ ρB σ pr))
                                   (wk^βιξη σ inc $ ρC σ pr))
                      × ((σ : ty) (pr : σ ∈ _) → EQREL _ σ (Normalise^βιξη ⊨⟦ ρA σ pr ⟧ ρB) (ρC σ pr)))
          (EQREL _ _)
SubstitutionNormaliseFusable =
  let module RenNorm = Fusion RenamingNormaliseFusable
      module EqNorm  = Synchronised SynchronisableNormalise in
  record
    { reifyA   = id
    ; RelEnv∙  = λ {_} {_} {_} {_} {ρA} {ρB} {ρC} ρR uR →
                     [ reflEQREL _ uR , proj₁ ρR ] 
                   , [ (λ {Θ} inc → wk^EQREL _ inc uR)
                     , (λ σ pr {Θ} inc →
                       transEQREL σ (RenNorm.fusion (ρA σ pr) (step refl) _ _
                                                    (λ σ pr → wk^EQREL σ inc (proj₁ ρR σ pr)))
                                    ((proj₁ ∘ proj₂) ρR σ pr inc)) ]
                     , [ uR , (λ σ pr → transEQREL σ (RenNorm.fusion (ρA σ pr) (step refl) _ _ (proj₁ ρR))
                                          ((proj₂ ∘ proj₂) ρR σ pr)) ]
    ; RelEnvWk = λ inc {ρA} ρR →
                            (λ σ pr → wk^EQREL σ inc (proj₁ ρR σ pr))
                          , (λ σ pr {Θ} inc′ →
                               transEQREL σ (EqNorm.synchronised (ρA σ pr)
                               (λ σ pr → transEQREL σ (wk^2 σ inc inc′ (proj₁ ρR σ pr))
                                                      (wk^EQREL σ (trans inc inc′) (proj₁ ρR σ pr))))
                               (transEQREL σ ((proj₁ ∘ proj₂) ρR σ pr (trans inc inc′))
                               (symEQREL σ (wk^2 σ inc inc′ (reflEQREL σ (symEQREL σ $ (proj₂ ∘ proj₂) ρR σ pr))))))
                          , (λ σ pr → (proj₁ ∘ proj₂) ρR σ pr inc)
    ; R⟦var⟧   = λ v _ _ _ ρR → (proj₂ ∘ proj₂) ρR _ v
    ; R⟦$⟧     = λ _ _ _ _ _ _ r → r refl
    ; R⟦λ⟧     = λ _ _ _ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ _ _ _ → tt
    ; R⟦tt⟧    = λ _ _ _ _ → PEq.refl
    ; R⟦ff⟧    = λ _ _ _ _ → PEq.refl
    ; R⟦ifte⟧  = ifteSubstNorm
    }
\end{code}


\section{Extensions and Future work}



\bibliography{main}

\end{document}
