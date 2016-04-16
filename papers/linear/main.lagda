\documentclass[a4paper,UKenglish]{lipics-v2016} 
%This is a template for producing LIPIcs articles. 
%See lipics-manual.pdf for further information.
%for A4 paper format use option "a4paper", for US-letter use option "letterpaper"
%for british hyphenation rules use option "UKenglish", for american hyphenation rules use option "USenglish"
% for section-numbered lemmas etc., use "numberwithinsect"

\input{commands}
\usepackage{agda}
\usepackage{mathpartir, lscape}
\usepackage{todonotes}
\usepackage{microtype}
\usepackage{catchfilebetweentags}
\lstset{
    escapeinside='',
    extendedchars=true,
    inputencoding=utf8,
}


\bibliographystyle{plainurl}% the recommended bibstyle

% Author macros::begin %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{Typing with Leftovers -- A mechanization of Intuitionistic Linear Logic\footnote{This work was partially supported by someone.}}
\titlerunning{Typing with Leftovers} %optional, in case that the title is too long; the running title should fit into the top page column

%% Please provide for each author the \author and \affil macro,
%% even when authors have the same affiliation, i.e. for each
%% author there needs to be the  \author and \affil macros
\author[1]{Guillaume Allais}
\affil[1]{Nijmegen Quantum Logic Group ─ Radboud University\\
  \texttt{gallais@cs.ru.nl}}
\authorrunning{G. Allais} %mandatory. First: Use abbreviated first/middle names. Second (only in severe cases): Use first author plus 'et. al.'

\Copyright{Guillaume Allais}
%mandatory, please use full first names.
% LIPIcs license is "CC-BY";  http://creativecommons.org/licenses/by/3.0/

\subjclass{Dummy classification -- please refer to \url{http://www.acm.org/about/class/ccs98-html}}
% mandatory: Please choose ACM 1998 classifications from http://www.acm.org/about/class/ccs98-html
% . E.g., cite as "F.1.1 Models of Computation".
\keywords{Dummy keyword -- please provide 1--5 keywords}% mandatory: Please provide 1-5 keywords
% Author macros::end %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Editor-only macros:: begin (do not touch as author)%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\EventEditors{John Q. Open and Joan R. Acces}
\EventNoEds{2}
\EventLongTitle{42nd Conference on Very Important Topics (CVIT 2016)}
\EventShortTitle{CVIT 2016}
\EventAcronym{CVIT}
\EventYear{2016}
\EventDate{December 24--27, 2016}
\EventLocation{Little Whinging, United Kingdom}
\EventLogo{}
\SeriesVolume{42}
\ArticleNo{23}
% Editor-only macros::end %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\maketitle

\begin{abstract}We start from a simple lambda-calculus and introduce a bidirectional 
typing relation corresponding to an Intuitionistic Linear Logic. This 
typing relation is based on the idea that a linear term consumes some 
of the resources available in its context whilst leaving behind leftovers 
which could then be used by another program. 

Practically, this means that typing derivations have both an input 
and an output context. This leads to a notion of weakening (all the 
extra resources added to the input context come out unchanged in the 
output one), a rather direct proof of stability under substitution, 
an analogue of the frame rule of separation logic showing that the 
state of unused resources can be safely ignored, as well as a proof 
that typechecking is decidable. 

The work has been fully formalised in Agda, commented source files 
are provided as additional material.
\end{abstract}


\section{Introduction}

\paragraph*{Notations} This whole development has been fully formalised
in Agda. Rather than including Agda syntax, the results are reformulated
in terms of definitions, lemmas, theorems, etc. However it is important
to keep in mind the distinction between various kinds of objects.
\texttt{Teletype} is used to denote data constructors, \DefinedType{small
capitals} are characteristic of defined types. A type families' index is
written as a subscript e.g. $\Var{}_n$.

\section{The Calculus of Raw Terms}

Following Altenkirch and Reus~\cite{altenkirch1999monadic},
we define the raw terms of our language not as an inductive
type but rather as an inductive \emph{family}~\cite{dybjer1994inductive}.
This technique, sometimes dubbed ``type-level de Bruijn indices'',
makes it possible to keep track, in the index of the familyn, of the
free variables currently in scope. As is nowadays folklore, instead of
using a set-indexed presentation where a closed terms is indexed by
the empty set $⊥$ and fresh variables are introduced by wrapping
the index in a \texttt{Maybe} type constructor\footnote{The value
\texttt{nothing} represents the fresh variable whilst the data
constructor \texttt{just} lifts all the existing ones in the new
scope.}, we index our terms by a natural number instead. The
\Var{} type family defined below represents the de Bruijn
indices~\cite{debruijn1972lambda} corresponding to the $n-1$ free
variables present in a scope $n$.

\begin{mathpar}
\inferrule
 {n : \Nat{}
}{\Var{}_n : \Set{}
}

\and \inferrule
 {
}{\texttt{zero} : \Var{}_{1 + n}
}

\and \inferrule
 {k : \Var{}_n
}{\texttt{suc} (k) : \Var{}_{1 + n}
}
\end{mathpar}

The calculus is presented in a bidirectional fashion\todo{cite}.
This gives a clean classification of term formers as being either
constructors of canonical values or eliminations corresponding to
computations. This separation also characterises the flow of
information during typechecking: given a context assigning a type
to each free variable, canonical values (which we call \Checkable{})
can be \emph{check}ed against a type whilst we may infer the type of
computations (which we call \Inferable{}).

\begin{figure}[h]\centering
\begin{tabular}{lcl}
⟨$\Inferable{}_n$⟩ & ::= & \texttt{var} ⟨$\Var{}_n$⟩ \\
                   &  |  & \texttt{app} ⟨$\Inferable{}_n$⟩ ⟨$\Checkable{}_n$⟩ \\
                   &  |  & \texttt{case} ⟨$\Inferable{}_n$⟩
                           \texttt{return} ⟨\Type{}⟩
                           \texttt{of} ⟨$\Checkable{}_{1 + n}$⟩
                           \texttt{\%\%} ⟨$\Checkable{}_{1 + n}$⟩ \\
                   &  |  & \texttt{cut} ⟨$\Checkable{}_n$⟩ ⟨\Type{}⟩ \\ \\

⟨$\Checkable{}_n$⟩ & ::= & \texttt{lam} ⟨$\Checkable{}_{1 + n}$⟩ \\
                   &  |  & \texttt{let} ⟨$\Pattern{}_m$⟩ \texttt{∷=} ⟨$\Inferable{}_n$⟩
                           \texttt{in} ⟨$\Checkable{}_{m + n}$⟩ \\
                   &  |  & \texttt{inl} ⟨$\Checkable{}_n$⟩ \\
                   &  |  & \texttt{inr} ⟨$\Checkable{}_n$⟩ \\
                   &  |  & \texttt{prd} ⟨$\Checkable{}_n$⟩ ⟨$\Checkable{}_n$⟩ \\
                   &  |  & \texttt{neu} ⟨$\Inferable{}_n$⟩ \\                  
\end{tabular}
\caption{Grammar of the Language of Raw Terms}
\end{figure}

Two additional rules (\texttt{neu} and \texttt{cut} respectively)
allow the embeddin of \Inferable{} into \Checkable{} and vice-versa. They
make it possible to form redexes by embedding canonical values into
computations and then applying eliminators to them. In terms of
typechecking, they correspond to a change of direction between
inferring and checking. The constructor \texttt{cut} takes an
extra \Type{} argument in order to guarantee the success of
type-inference for \Inferable{} terms.

A notable specificity of this language is the ability to use nested
patterns in a let binder rather than having to resort to cascading
lets. This is achieved thanks to a rather simple piece of kit: the
\Pattern{} type family. A value of type $\Pattern{}_n$ represents a
pattern binding $n$ variables. Because variables are represented as
de Bruijn indices, the base pattern does not need to be associated
with a name, it simply is a constructor \texttt{v} binding exactly
$1$ variable. The comma pattern constructor takes two nested patterns
respectively binding $m$ and $n$ variable and uses them to deeply
match a pair thus binding $(m + n)$ variables.

\begin{mathpar}
\inferrule
 {n : \Nat{}
}{\Pattern{}_n : \Set{}
}

\and \inferrule
 {
}{\texttt{v} : \Pattern{}_1
}

\and \inferrule
 {p : \Pattern{}_m \and q : \Pattern{}_n
}{p \texttt{,} q : \Pattern{}_{m + n}
}
\end{mathpar}

The grammar of raw terms only guarantees that all expressions are
well-scoped by construction. It does not impose any other constraint,
which means that a user may write valid programs but also invalid
ones as the following examples demonstrate:

\begin{example}\label{example:swap}
\texttt{swap} is a closed, well-typed linear term taking a pair as
an input and swapping its components. It corresponds to the mathematical
function $(x, y) \mapsto (y, x)$.
\begin{lstlisting}
  swap = lam (let (v , v) ∷= var zero
              in prd (neu (var (suc zero))) (neu (var zero)))
\end{lstlisting}
\end{example}

\begin{example}\label{example:illTyped}
\texttt{illTyped} is a closed linear term. However it is manifestly
ill-typed: the let-binding it uses tries to break down a function as
if it were a pair.
\begin{lstlisting}
  illTyped = let (v , v) ∷= cut (lam (neu (var zero))) (a ⊸ a)
             in prd (neu (var zero)) (neu (var (suc zero)))
\end{lstlisting}
\end{example}

\begin{example}\label{example:diagonal}
Finally, \texttt{diagonal} is a term typable in the simply-typed
lambda calculus but it is not linear: it duplicates its input just
like $x \mapsto (x, x)$ does.
\begin{lstlisting}
  diagonal = lam (prd (neu (var zero)) (neu (var zero)))
\end{lstlisting}
\end{example}

\section{Linear Typing Rules}

These considerations lead us to the need for a typing relation
describing the rules terms need to abide by in order to qualify
as valid programs. A linear type system is characterised by the
fact that all the resources available in a context have to be
used exactly once by the term being checked. In traditional
presentations of linear logic this is achieved by representing
the context as a multiset and, in each rule, cutting it up and
distributing its parts among the premises. This is epitomised
by the introduction rule for tensor (cf. Figure~\ref{rule:tensor}).

However, multisets are an intrinsically extensional notion and
therefore quite arduous to work with in an intensional type
theory. Various strategies can be applied to tackle this issue;
most of them rely on using linked lists to represent contexts
together with either extra inference rules to reorganise the
context or a side condition to rules splitting the context so
that it may be re-arranged on the fly. In the following example
$\_≈\_$ stands for ``bag-equivalence'' of lists.
\begin{figure}[h]
\begin{mathpar}
\inferrule
 {Γ ⊢ σ \and Δ ⊢ τ
}{Γ, Δ ⊢ σ ⊗ τ
}{⊗_i}

\and \inferrule
 {Γ ⊢ σ \and Δ ⊢ τ \and Γ, Δ ≈ Θ
}{Θ ⊢ σ ⊗ τ
}{⊗_i}
\end{mathpar}
\caption{Introduction rules for tensor (left: usual presentation, right: with reordering on the fly)\label{rule:tensor}}
\end{figure}

All of these strategies are artefacts of the unfortunate mismatch
between the ideal mathematical objects one wishes to model and
their internal representation in the proof assistant. Short of
having proper quotient types, this will continue to be an issue
when dealing with multisets. The solution described in the rest
of this paper tries not to replicate a set-theoretic approach in
intuitionistic type theory but rather strives to find the type
theoretical structures which can make the problem more tractable.
Indeed, given the right abstractions most proofs become simple
structural inductions.

\subsection{Usage Annotations}

McBride's recent work~\cite{mcbride2016got} on combining linear and
dependent types highlights the distinction one can make between
referring to a resource and actually consuming it. In the same spirit,
rather than dispatching the available resources in the appropriate
subderivations, we consider that a term is checked in a \emph{given}
context on top of which usage annotations are super-imposed. These
usage annotations indicate whether resources have been consumed already
or are still availble. Type-inference (resp. Type-checking) is then
inferring (resp. checking) a term's type but \emph{also} annotating
the resources consumed by the term in question and returning the
\emph{leftovers} which gave their name to this paper.

\begin{definition}
\label{definition:context}
A \Context{} is a list of \Type{}s indexed by its length. It can
be formally described by the following inference rules:
\begin{mathpar}
\inferrule
 {n : \Nat{}
}{\Context{}_n : \Set{}
}

\and \inferrule
 {
}{[] : \Context{}_0
}

\and \inferrule
 {γ : \Context{}_n \and σ : \Type{}
}{γ ∙ σ : \Context{}_{1 + n}
}
\end{mathpar}
\end{definition}


\begin{definition}
\label{definition:usage}
A \Usage{} is a predicate on a type σ describing whether the
resource associated to it is available or not. We name the
constructors describing these two states \texttt{fresh} and
\texttt{stale} respectively. The pointwise lifting of \Usage{}
to contexts is called \Usages{}. The inference rules are:
\begin{mathpar}
\inferrule
 {σ : \Type{}
}{\Usage{}_σ : \Set{}
}
\and\inferrule
 {
}{\texttt{fresh}_σ : \Usage{}_σ
}
\and\inferrule
 {
}{\texttt{stale}_σ : \Usage{}_σ
}
\end{mathpar}
\begin{mathpar}
\inferrule
 { γ : \Context{}_n
}{\Usages{}_γ : \Set{}
}
\and\inferrule
 {
}{[] : \Usages{}_{[]}
}
\and\inferrule
 {Γ : \Usages{}_γ \and S : \Usage{}_σ
}{Γ ∙ S : \Usages{}_{γ ∙ σ}
}
\end{mathpar}
\end{definition}

\subsection{Typing as Consumption Annotation}

A Typing relation seen as a consumption annotation process describes
what it means, given a context an its usage annotation, to ascribe a
type to a term whilst crafting another usage annotation containing all
the leftover resources. Formally:

\begin{definition}
\label{definition:typing}
A ``Typing Relation'' for $T$ a \Nat{}-indexed inductive family is
an indexed relation $\text{\𝓣{}}_n$ such that:
\begin{mathpar}
\inferrule
 {n : \Nat{} \and γ : \Context{}_n \and Γ, Δ : \Usages{}_γ \and t : T_n \and σ : \Type{}
}{\text{\𝓣{}}_n(Γ, t, σ, Δ) : \Set{}
}
\end{mathpar}
\end{definition}

This definition clarifies the notion but also leads to more generic
statements later on: weakening, substitutiong, framing can all be
expressed as properties a Typing Relation might have.

\input{typing-rules}

\subsubsection{Typing de Bruijn indices}

The simplest instance of a Typing Relation is the one for de Bruijn
indices: given an index $k$ and a usage annotation, it successfully
associates a type to that index if and only if the $k$th resource
in context is \texttt{fresh}. In the resulting leftovers, the resource
will have turned \texttt{stale}:

\begin{definition}
\label{typing:deBruijn}
The typing relation is presented in a sequent-style: Γ ⊢ $k$ ∈ σ ⊠ Δ
means that starting from the usage annotation Γ, the de Bruijn index
$k$ is ascribed type σ with leftovers Δ. It is defined inductively by
two constructors (cf. Figure~\ref{figure:deBruijn}).
\end{definition}

\begin{remark}The careful reader will have noticed that there is precisely
one typing rule for each \Var{} constructor. It is not a coincidence. And
if these typing rules are not named it's because in Agda, they can simply
be given the same name as their \Var{} counterpart. The same will be true
for \Inferable{}, \Checkable{} and \Pattern{} which means that writing
down a typable program could be seen as either writing a raw term or the
typing derivation associated to it depending on the author's intent.
\end{remark}

\begin{example}
The de Bruijn index 1 has type τ in the context (γ ∙ σ ∙ τ) with
usage annotation ($Γ ∙ \texttt{fresh}_τ ∙ \texttt{fresh}_σ$):
\begin{mathpar}
\inferrule
 {\inferrule
   {
  }{Γ ∙ \texttt{fresh}_τ ⊢ \texttt{zero} ∈ τ ⊠ Γ ∙ \texttt{stale}_τ
  }
}{Γ ∙ \texttt{fresh}_τ ∙ \texttt{fresh}_σ ⊢ \texttt{suc(zero)} ∈ τ ⊠ Γ ∙ \texttt{stale}_τ ∙ \texttt{fresh}_σ
}
\end{mathpar}
Or, as it would be written in Agda, taking advantage of the fact that
the language constructs and the typing rules about them have been given
the same names:
\begin{lstlisting}
  one : 'Γ' '∙' fresh 'τ' '∙' fresh 'σ' ⊢ suc(zero) '∈' 'τ' '⊠' 'Γ' '∙' stale 'τ' '∙' fresh 'σ'
  one = suc zero
\end{lstlisting}
\end{example}

\subsubsection{Typing terms}

The key idea appearing in all the typing rules for compound
expressions is to use the input \Usages{} to type one of the
sub-expressions, collect the leftovers from that typing
derivation and use them as the new input \Usages{} when typing
the next sub-expression.

Another common pattern can be seen across all the rules involving
binders, be they λ-abstractions, let-bindings or branches of a
case. Typechecking the body of a binder involves extending the
input \Usages{} with fresh variables and observing that they have
become stale in the ouput one. This guarantees that these bound
variables cannot escape their scope as well as that they have indeed
been used. Relaxing the staleness restriction would lead to an affine
type system which would be interesting in its own right.

\begin{definition}The Typing Relation for \Inferable{} is typeset
in a fashion similar to the one for \Var{}. Indeed, in both cases
the type is inferred. $Γ ⊢ t ∈ σ ⊠ Δ$ means that given Γ a
$\Usages{}_γ$, and $t$ an \Inferable{}, the type σ is inferred
together with leftovers Δ, another $\Usages{}_γ$. The rules are
listed in Figure~\ref{figure:infer}.

For \Checkable{}, the type σ comes first: $Γ ⊢ σ ∋ t ⊠ Δ$ means
that given Γ a $\Usages{}_γ$, a type σ, the \Checkable{} $t$ can
be checked to have type σ with leftovers Δ. The rules can be found
in Figure~\ref{figure:check}.
\end{definition}

\begin{example}
Given these rules, it is easy to see that the identity function
can be checked at type (σ ⊸ σ) in an empty context:
\begin{mathpar}
\inferrule
 {\inferrule
   {\inferrule
     {\inferrule
       {
      }{[] ∙ \texttt{fresh}_σ ⊢ \texttt{zero} ∈ σ ⊠ [] ∙ \texttt{stale}_σ
      }
    }{[] ∙ \texttt{fresh}_σ ⊢ \texttt{var}(\texttt{zero}) ∈ σ ⊠ [] ∙ \texttt{stale}_σ
    }
  }{[] ∙ \texttt{fresh}_σ ⊢ σ ∋ \texttt{neu}(\texttt{var}(\texttt{zero})) ⊠ [] ∙ \texttt{stale}_σ
  }
}{[] ⊢ σ ⊸ σ ∋ \texttt{lam}(\texttt{neu}(\texttt{var}(\texttt{zero}))) ⊠ []
}
\end{mathpar}
Or, as it would be written in Agda where the typing rules were
given the same name as their term constructor counterparts:
\begin{lstlisting}
  identity : [] '⊢' 'σ' '⊸' 'σ' '∋' lam (neu (var zero)) '⊠' []
  identity = lam (neu (var zero))
\end{lstlisting}
\end{example}

\begin{example}
It is also possible to revisit Example \ref{example:swap} to prove
that it can be checked against type (σ ⊗ τ) ⊸ (τ ⊗ σ) in an empty
context. This gives the lengthy derivation included in the appendix
or the following one in Agda which quite a lot more readable:

\begin{lstlisting}
  swapTyped : [] '⊢' ('σ' '⊗' 'τ') '⊸' ('τ' '⊗' 'σ') '∋' swap '⊠' []
  swapTyped = lam (let (v , v) ∷= var zero
                   in prd (neu (var (suc zero))) (neu (var zero))
\end{lstlisting}
\end{example}

%%%%%%%%%%%%%
%% FRAMING %%
%%%%%%%%%%%%%

\section{Framing}

The most basic property one can prove about this typing system is
the fact that the state of the resources which are not used by a
lambda term is irrelevant. We call this property the Framing
Property because of the obvious analogy with the frame rule in
separation logic. This can be reformulated as the fact that as
long as two pairs of an input and an output usages exhibit the
same consumption pattern then if a derivation uses one of these,
it can use the other one instead. Formally (postponing the
definition of $Γ - Δ ≡ Θ - ξ$):

\begin{definition}A Typing Relation \𝓣{} for a \Nat{}-indexed
family $T$ has the Framing Property if for all $k$ a \Nat{},
γ a $\Context{}_k$, Γ, Δ, Θ, ξ four $\Usages{}_γ$, $t$ an element
of $T_k$ and σ a Type, if $Γ - Δ ≡ Θ - ξ$ and \𝓣{}$(Γ, t, σ, Δ)$
then \𝓣{}$(Θ, t, σ, ξ)$ also holds.
\end{definition}



\begin{definition}
\label{definition:differences}
The ``consumption equivalence'' characterises the pairs of an input and
an output \Usages{} which have the same consumption pattern. The
usages annotations for the empty context are trivially related.
If the context is not empty, then there are two cases: if the
resources is left untouched on side, then so should it on the other
side but the two annotations may be different (here denoted $A$ and $B$
respectively). On the other hand, if the resource has been consumed
on one side then it has to be on the other side too.
\begin{mathpar}
\inferrule
 {Γ, Δ, Θ, ξ : \Usages{}_γ
}{Γ ─ Δ ≡ Θ ─ ξ : \Set{}
}
\and \inferrule
 {
}{[] - [] ≡ [] - []
}{
}
\and \inferrule
 {Γ - Δ ≡ Θ - ξ
}{(Γ ∙ A) - (Δ ∙ A) ≡ (Θ ∙ B) - (ξ ∙ B)
}{
}
\and \inferrule
 {Γ - Δ ≡ Θ - ξ
}{(Γ ∙ \texttt{fresh}_σ) - (Δ ∙ \texttt{stale}_σ) ≡ (Θ ∙ \texttt{fresh}_σ) - (ξ ∙ \texttt{stale}_σ)
}{
}
\end{mathpar}
\end{definition}

\begin{definition}The ``consumption partial order'' $Γ ⊆ Δ$ is defined as
$Γ - Δ ≡ Γ - Δ$.
\end{definition}

\begin{lemma}
\begin{enumerate}
  \item The consumption equivalence is a partial equivalence
  \item The consumption partial order is a partial order
  \item If there is a Usages ``in between'' two others according to the consumption
        partial order, then any pair of usages equal to these two can be split in a
        manner compatible with this middle element. Formally: Given Γ, Δ, Θ, ξ
        and χ such that $Γ - Δ ≡ Θ - ξ$, $Γ ⊆ χ$ and $χ ⊆ Δ$,
        one can find ζ such that: $Γ - χ ≡ Θ - ζ$ and $χ - Δ ≡ ζ - ξ$.
\end{enumerate}
\end{lemma}

\begin{lemma}[Consumption]The Typing Relations for \Var{}, \Inferable{}
and \Checkable{} all imply that if a typing derivation exists with input
usages annotation Γ and output usages annotation Δ then $Γ ⊆ Δ$.
\end{lemma}

\begin{theorem}
\label{theorem:framing}
The Typing Relations for \Var{} has the Framing Property.
So do the ones for \Inferable{} and \Checkable{}.
\end{theorem}
\begin{proof}
The proofs are by structural induction on the typing derivations.
They rely on the previous lemmas to generate the inclusion evidence
and use it to split up the witness of consumption equivalence and
distribute it appropriately in the induction hypotheses.
\end{proof}

%%%%%%%%%%%%%%%
%% WEAKENING %%
%%%%%%%%%%%%%%%

\section{Weakening}

It is perhaps surprising to find a notion of weakening for a linear
calculus: the whole point of linearity is precisely to ensure that
all the resources are used. However when opting for a system based
on consumption annotations it becomes necessary, in order to define
substitution for instance, to be able to extend the underlying
context a term is defined with respect to. Linearity is guaranteed
by ensuring that the inserted variables are left untouched by the
term.

Weakening arises from a notion of inclusion. The appropriate type
theoretical structure to describe these inclusions is well-known
and called an Order Preserving Embeddding~\cite{chapman2009thesis,altenkirch1995categorical}.
Unlike a simple function witnessing the inclusion of its domain
into its codomain, the restriction brought by order preserving
embeddings guarantees that contraction is simply not possible which
is crucial in a linear setting. In this development, three variations
on OPEs are actually needed: one for \Nat{}s to describe the embedding
of a scope into a larger one, one for \Context{} describing what types
the extra variables in scope are assigned and finally one for their
\Usages{} mentioning whether these variables are fresh or stale.

\begin{definition}
An Order Preserving Embedding is an inductive family. Its constructors
dubbed ``moves'' describe a strategy to realise the promise of an
embedding. Figure~\ref{figure:ope} defines three OPEs at the same
time.

The first column lists the name of constructors associated to each
one of the moves. The second column describes the OPE for \Nat{}s
and it follows closely the traditional definition of OPEs. The two
remaining columns are a bit different: they respectively define the
OPE for \Context{}s and the one for \Usages{}. However they do not
mention the source and target sets in their indices; they are in
fact generic enough to be applied to any context / usages of the
right size. If a value of $k ≤ l$ is seen as a \emph{diff} between
$k$ and $l$ then the OPEs on contexts and usages annotations only
specify what to do for the variables introduced by the diff (i.e.
the variables corresponding to an \texttt{insert} constructor).
These diffs can then be applied to concrete contexts and usages
respectively to transform them.

The first row defines the move \texttt{done} for each one of the
OPEs. It is the strategy corresponding to the trivial embedding of
a set into itself by the identity. It serves as a base case.

The second row corresponds to the \texttt{copy} move which extends
an existing embedding by copying the current $0$th variable from
source to target. The corresponding cases for \Context{}s and
\Usages{} are purely structural: no additional content is required
to be able to perform a \texttt{copy} move.

Last but not least, the third row describes the move \texttt{insert}
which introduces an extra variable in the target set. This is the
move used to extend an existing context, i.e. to weaken it. In this
case, it is paramount that the OPE for \Context{}s should take a
type σ as an extra argument (it will be the type of the newly introduced
variable) whilst the OPE for \Usages{} takes a $\Usage{}_σ$ (it will
be the usage associated to that newly introduced variable of type σ).

\begin{figure}\centering
\begin{tabular}{l|c|c|c}
& \inferrule
 {k, l : \Nat{}
}{k ≤ l : \Set{}
}
& \inferrule
 {o : k ≤ l 
}{\OPE{}(o) : \Set{}
}
& \inferrule
 {o : k ≤ l \and O : \OPE{}(o)
}{\OPE{}(O) : \Set{}
} \\ & & \\
\texttt{done}
& \inferrule
 {
}{k ≤ k
}
& \inferrule
 {
}{\OPE{}(\texttt{done})
}
& \inferrule
 {
}{\OPE{}(\texttt{done})
}\\ & & \\
\texttt{copy}
& \inferrule
 {k ≤ l
}{1+k ≤ 1+l
}
& \inferrule
 {o : k ≤ l \and \OPE{}(o)
}{\OPE{}(\texttt{copy}(o))
}
& \inferrule
 {{\begin{array}{l}o : k ≤ l \\ O : \OPE{}(o)\end{array}} \and \OPE{}(O)
}{\OPE{}(\texttt{copy}(O))
}\\ & & \\
\texttt{insert}
& \inferrule
 {k ≤ l
}{k ≤ 1+l
}
& \inferrule
 {o : k ≤ l \and \OPE{}(o) \and \Type{}
}{\OPE{}(\texttt{insert}(o))
}
& \inferrule
 {{\begin{array}{l}o : k ≤ l \\ O : \OPE{}(o) \\ σ : \Type{}\end{array}} \and \OPE{}(O) \and S : \Usage{}_σ
}{\OPE{}(\texttt{insert}(O, σ))
}
\end{tabular}
\caption{Order Preserving Embeddings for \Nat{}, \Context{} and \Usages{}\label{figure:ope}}
\end{figure}
\end{definition}

\begin{example}
\label{example:ope}
We may define three embeddings corresponding to the introduction of a
fresh variable for scopes, contexts and usages respectively. The
body of these three declarations looks the same because we overload
the constructors' names but they build different objects. As can be
seen in the types, the latter ones depend on the former ones. This
type of embedding is very much grounded in reality: it is precisely
what pushing a substitution under a lambda abstraction calls for.
\begin{lstlisting}
  scopeWithFV : suc n '≤' suc (suc n)
  scopeWithFV = insert done

  contextWithFV : Type '→' Context.OPE scopeWithFV
  contextWithFV 'σ' = insert done 'σ'

  usagesWithFV : ('σ' : Type) '→' Usage σ '→' Usages.OPE (contextWithFV 'σ')
  usagesWithFV 'σ' S = insert done S
\end{lstlisting}
\end{example}

We leave out the definitions of the two \texttt{patch} functions applying
the diff described by an OPE to respectively a context or a usages
annotation. They are structural in the OPE. The interested reader will find
them in the formal development in Agda. We also leave out the definition of
weakening for raw terms. It is given by a simple structural induction on the
terms themselves.

\begin{definition}A Typing Relation \𝓣{} for a \Nat{}-indexed family $T$
such that we have a function $\texttt{weak}_T$ transporting proofs that
$k ≤ l$ to functions $T_k → T_l$ is said to have the Weakening Property
if for all $k, l$ in \Nat{}, $o$ a proof that $k ≤ l$, $O$ a proof that
$\OPE{}(o)$ and $𝓞$ a proof that $\OPE{}(O)$ then for all γ a $\Context{}_k$,
Γ and Δ two $\Usages{}_γ$, $t$ an element of $T_k$ and σ a \Type{}, if
\𝓣{}$(Γ, t, σ, Δ)$ holds true then we also have
\𝓣{}$(\texttt{patch}(𝓞, Γ), \texttt{weak}_T(o, t), σ, \texttt{patch}(𝓞, Δ))$.
\end{definition}

\begin{theorem}The Typing Relation for \Var{} has the Weakening Property.
So do the Typing Relations for \Inferable{} and \Checkable{}.
\end{theorem}
\begin{proof}
The proof for \Var{} is by induction on the typing derivation. The
statements for \Inferable{} and \Checkable{} are proved by mutual
structural inductions on the respective typing derivations. Using the
\texttt{copy} constructor of OPEs is crucial to be able to go under
binders.
\end{proof}



%%%%%%%%%%%%%%%%%%
%% SUBSTITUTION %%
%%%%%%%%%%%%%%%%%%

\section{Substituting}

Stability of the typing relation under substitution guarantees
that the evaluation of programs will yield results which have
the same type as well as preserve the linearity constraints.
The notion of leftovers naturally extends to substitutions: the
terms meant to be substituted for the variables in context which
are not used by a term will not be used when pushing the substitution
onto this term. They will therefore have to be returned as leftovers.

Because of this rather unusual behaviour for substitution, picking
the right type-theoretical representation for the environment
carrying the values to be substituted in is a bit subtle. Indeed,
relying on the usual combination of weakening and crafting a fresh
variale when going under a binder becomes problematic. The leftovers
returned by the induction hypothesis would then live in an extended
context and quite a lot of effort would be needed to downcast them
back to the smaller context they started in. The solution is to have
an explicit constructor for ``going under a binder''. 

\begin{definition}The environment \Env{} used to define substitution
for raw terms is indexed by two variables $k$ and $l$ where $k$ is the
source's scope and $l$ is the target's scope. There are three constructors:
one for the empty environment ([]), one for going under a binder (\texttt{∙v})
and one to extend an environment with an $\Inferable{}_l$.
\begin{mathpar}
\inferrule
 {
}{[] : \Env{}(0, l)
}
\and \inferrule
 {ρ : \Env{}(k, l)
}{ρ \texttt{∙v} : \Env{}(\texttt{suc}(k), \texttt{suc}(l)) 
}
\and \inferrule
 {ρ : \Env{}(k, l) \and t : \Inferable{}_l
}{ρ ∙ t : \Env{} (\texttt{suc}(k), l)
}
\end{mathpar}
\end{definition}

\begin{theorem}[Stability under Substitution]
\label{theorem:substituting}
\end{theorem}

%%%%%%%%%%%%%%%%%%
%% TYPECHECKING %%
%%%%%%%%%%%%%%%%%%

\section{Typechecking}

\begin{theorem}[Decidability of Typechecking]
\label{theorem:typechecking}
\end{theorem}


%%%%%%%%%%%%%%%%%%
%% RELATED WORK %%
%%%%%%%%%%%%%%%%%%

\section{Related Work}

We have already mentioned McBride's work~\cite{mcbride2016got}
on (as a first approximation: the setup is actually more general)
a type theory with a \emph{dependent linear} function space as a
very important source of inspiration. In that context it is indeed
crucial to retain the ability to tlak about a resource even if it
has already been consumed. E.g. a function taking a boolean and
deciding wheter it is equal to \texttt{tt} or \texttt{ff} will
have a type mentioning the function's argument twice. But in a
lawful manner: $(x : \DefinedType{Bool}) ⊸ (x ≡ \texttt{tt}) ∨ (x ≡ \texttt{ff})$.
This leads to the need for a context \emph{shared} across all
subterms and consumption annotations ensuring that the linear
resources are never used more than once.

We can find a very concrete motivation for a predicate similar to
our \Usage{} in Robbert Krebbers' thesis~\cite{krebbers2015thesis}.
In section 2.5.9, he describes one source of undefined behaviours
in the C standard: the execution order of expressions is unspecified
thus leaving the implementers with absolute freedom to pick any order
they like if that yields better performances. To make their life
simpler, the standard specifies that no object should be modified
more than once during the execution of an expression. In order to
enforce this invariant, the memory model is enriched with extra
information:
\begin{quote}
  [E]ach bit in memory carries a permission that is set to a special
  locked permission when a store has been performed. The memory
  model prohibits any access (read or store) to objects with locked
  permissions. At the next sequence point, the permissions of locked
  objects are changed back into their original permission, making
  future accesses possible again.
\end{quote}



%%
%% Bibliography
%%

%% Either use bibtex (recommended),

\bibliography{main}

%% .. or use the thebibliography environment explicitely

\appendix

\begin{landscape}
\input{typing-swap}
\end{landscape}

\end{document}
