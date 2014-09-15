\documentclass[a4paper, twocolumn]{article}
\usepackage{amsthm, amsmath}
\usepackage{mathpartir}
\usepackage[english]{babel}
\usepackage[references]{agda}
\usepackage{hyperref}

\usepackage{todonotes}

\usepackage{float}
\floatstyle{boxed}
\restylefloat{figure}

\setmainfont{XITS}
\setmathfont{XITS Math}

\input{commands.tex}

\title{Resource-Aware Contexts and Certified Proof Search for
Intuitionistic Multiplicative Linear Logic}

\begin{document}
\maketitle

\begin{abstract}
In this article we show the difficulties a type-theorist
may face when attempting to formalise a decidability result
described informally. We then demonstrate how generalising
the problem and switching to a more structured presentation
can alleviate her suffering.

The calculus we target is a fragment of Intuitionistic
Multiplicative Linear Logic (IMLL onwards) and the tool we
use to construct the search procedure is Agda (but any
reasonable type theory equipped with data types could do).
We believe the approach described here can be used in other
settings.
\end{abstract}

\section{Introduction}

Type theory is expressive enough that one can implement
\emph{certified} proof search algorithms which are not
merely oracles outputting a one bit answer but full-blown
automated provers producing derivations which are
statically known to be correct. It is only natural to delve
into the litterature to try and find decidability proofs
which, through the curry-howard correspondence, could make
good candidates for mechanisation. Reality is however not
as welcoming as one would hope: most of these proofs have
not been formulated with formalisation in mind and would
require a huge effort to be ported \emph{as is} in your
favourite theorem prover.

In this article, we argue that it would indeed be a grave
mistake to implement them \emph{as is} and that type-theorists
should aim to develop better-structured algorithms. We show,
working on a fragment of IMLL~\cite{girard1987linear}, the sort
of pitfalls to avoid and the generic ideas leading to better-behaved
formulations.
In \autoref{sec:IMLL} we describe the fragment of IMLL we are
studying; \autoref{sec:general} defines a more general calculus
internalising the notion of leftovers and \autoref{sec:contexts}
introduces resource-aware contexts thus giving us a powerful
language to target with our proof search algorithm. The soudness
result proved in \autoref{sec:soundness} is what lets us recover
an IMLL proof from one expressed in the more general system.


\section{The Calculus, Informally\label{sec:IMLL}}

The calculus we are considering is a fragment of Intuitionistic
Multiplicative Linear Logic composed of \textit{atomic} types,
\textit{tensor} products and \textit{with}. This is summed up
by the following grammar for types:

$$
\text{\AD{ty} ~∷=~ \AIC{κ} \AD{ℕ} ~|~ \AD{ty} \tensor{} \AD{ty}
                                  ~|~ \AD{ty} \with{} \AD{ty}}
$$

The calculus' sequents (\AB{Γ} \entails{} \AB{σ}) are composed of
a multiset of types (\AB{Γ}) describing the resources available in
the context and a type (\AB{σ}) corresponding to the proposition
one is trying to prove. Each type constructor comes with both
introduction and elimination rules described in \autoref{fig:IMLLRules}.

\begin{figure*}[h]
\begin{mathpar}
\inferrule{ }{\text{\lmulti{} \AB{σ} \rmulti{} \entails{} \AB{σ}}}{ax}

\and
\inferrule{
     \text{\AB{Γ} \entails{} \AB{σ}}
\and \text{\AB{Δ} \entails{} \AB{τ}}
}{   \text{\AB{Γ} \disjoint{} \AB{Δ} \entails{} \AB{σ} \tensor{} \AB{τ}}
}{\tensor{}^r}

\and
\inferrule{
     \text{\AB{Γ} \disjoint{} \lmulti{} \AB{σ}, \AB{τ} \rmulti{} \entails{} \AB{υ}}
}{   \text{\AB{Γ} \disjoint{} \lmulti{} \AB{σ} \tensor{} \AB{τ} \rmulti{} \entails{} \AB{υ}}
}{\tensor{}^l}
\end{mathpar}
\begin{mathpar}
\inferrule{
     \text{\AB{Γ} \entails{} \AB{σ}}
\and \text{\AB{Γ} \entails{} \AB{τ}}
}{   \text{\AB{Γ} \entails{} \AB{σ} \with{} \AB{τ}}
}{\with{}^r}

\and
\inferrule{
     \text{\AB{Γ} \disjoint{} \lmulti{} \AB{σ} \rmulti{} \entails{} \AB{υ}}
}{   \text{\AB{Γ} \disjoint{} \lmulti{} \AB{σ} \with{} \AB{τ} \rmulti{} \entails{} \AB{υ}}
}{\with{}_1^l}

\and
\inferrule{
     \text{\AB{Γ} \disjoint{} \lmulti{} \AB{τ} \rmulti{} \entails{} \AB{υ}}
}{   \text{\AB{Γ} \disjoint{} \lmulti{} \AB{σ} \with{} \AB{τ} \rmulti{} \entails{} \AB{υ}}
}{\with{}_2^l}
\end{mathpar}
\caption{Introduction and Elimination rules for IMLL\label{fig:IMLLRules}}
\end{figure*}

\section{Generalising the Problem\label{sec:general}}

Rather than sticking to the original presentation and
trying to work around the inconvenience of dealing with
intrinsically extensional notions such as the one of
multisets, it is possible to generalise the calculus
in order to have a more palatable formal treatment.

The principal insight in this development is that proof
search in Linear Logic is not just about fully using the
context provided to us as an input in order to discharge
a goal. The bulk of the work is rather to use parts of
some of the assumptions of a context to discharge a first
subgoal; collect the leftovers and invest them into trying
to discharge another subproblem. Only in the end should the
leftovers be down to nothing.

This observation leads to the definition of two new notions:
first, the calculus is generalized to one incorporating the
notion of leftovers; second, the contexts are made
resource-aware meaning that they keep the same structure
whilst tracking whether (parts of) an assumption has been
used already. In this section, we will start by studying a
simple example showcasing this idea and then dive into the
implementation details of such concepts.

\subsection{Example\label{example}}

In the following paragraphs, we are going to study how one
would describe the process of running a proof search algorithm
trying to produce a derivation of type
(\AB{σ} \tensor{} \AB{τ}) \with{} \AB{σ} \entails{} \AB{τ} \tensor{} \AB{σ}
where \AB{σ} and \AB{τ} are assumed to be atomic. In order to
materialise the idea that some resources are consumed whilst
discharging subgoals, we are going to mark with a box \fba{ }
(the parts of) the assumptions which have been used.

The goal's head symbol is a \tensor{}; let us start by looking
for a proof of its left part. Given that \AB{τ} is an atomic
formula, the only way to discharge this goal is to use an
assumption available in the context. Luckily for us, there is
a \AB{τ} in the context; we are therefore able to produce the
following derivaton:
\begin{mathpar}
\inferrule{
}{\text{(\AB{σ} \tensor{} \fba{\AB{τ}}) \with{} \AB{σ} \entails{} \AB{τ}}
}{ax}
\end{mathpar}
Now that we are done with the left subgoal, we can deal with
the right. The main difference is that our available context
is not (\AB{σ} \tensor{} \AB{τ}) \with{} \AB{σ} anymore but
rather the consumption annotated (\AB{σ} \tensor{} \fba{\AB{τ}}) \with{} \AB{σ}.
We are once more facing an atomic formula which we can only
discharge by using an assumption. This time there are two
candidates in the context; except that one of them is inaccessible:
solving the previous goal has had the side-effect of picking one
side of the \with{} thus rejecting the other entirely. The only
derivation we can produce is therefore:
\begin{mathpar}
\inferrule{
}{\text{(\fba{\AB{σ}} \tensor{} \fba{\AB{τ}}) \with{} \AB{σ} \entails{} \AB{σ}}
}{ax}
\end{mathpar}
We can then combine these two by using a right introduction
rule for \tensor{}. If we add an extra, englobing, box every
time an entire subpart of an assumption is used, we end up
with a tree whose conclusion is:
\begin{mathpar}
\inferrule{\vdots{} \and \vdots{}
}{\text{\fbc{\fbb{(\fba{\AB{σ}} \tensor{} \fba{\AB{τ}})} \with{} \AB{σ}}
        \entails{} \AB{τ} \tensor{} \AB{σ}}
}{\tensor{}^r}
\end{mathpar}
The fact that the whole context is used by the end of the search
tells us that this translates into a valid IMLL proof tree. And
it is indeed the case: by following the structure of the pseudo-proof
we just generated above and adding the required left rules\footnote{We
will explain in \autoref{sec:soundness} how deciding where these left
rules should go can be done automatically}, we get the following
derivation.
\begin{mathpar}
\inferrule{
 \inferrule{
  \inferrule{
        \inferrule{ }{\text{\AB{τ} \entails{} \AB{τ}}}{ax}
   \and \inferrule{ }{\text{\AB{σ} \entails{} \AB{σ}}}{ax}
  }{\text{\AB{σ}, \AB{τ} \entails{} \AB{τ} \tensor{} \AB{σ}}
  }{\tensor{}^r}
 }{\text{\AB{σ} \tensor{} \AB{τ} \entails{} \AB{τ} \tensor{} \AB{σ}}
 }{\tensor{}^l}
}{\text{(\AB{σ} \tensor{} \AB{τ}) \with{} \AB{σ} \entails{} \AB{τ} \tensor{} \AB{σ}}
}{\with{}_1^l}
\end{mathpar}

\subsection{A Calculus with Leftovers}

This observation of a proof search algorithm in action leads
us to the definition of a three place relation describing the
new calculus where the notion of leftovers from a subproof is
internalised. When we write \AB{Γ} \entails{} \AB{σ} \coentails{}
\AB{Δ}, we mean that from the input \AB{Γ}, we can prove \AB{σ}
with leftovers \AB{Δ}.

If we assume that we already have in our possesion a similar relation
\AB{Γ} \belongs{} \AB{k} \cobelongs{} \AB{Δ} describing the act of
consuming a resource \AIC{κ} \AB{k}\footnote{In this presentation,
we limit the axiom rule to atomic formulas only but it is not an
issue: it is a well-known fact that more general rules are admissible
by a simple induction on the goal's type.} from a context \AB{Γ}
with leftovers \AB{Δ}, then the axiom rule translates to:
\begin{mathpar}
\inferrule{\text{\AB{Γ} \belongs{} \AB{k} \cobelongs{} \AB{Δ}}
}{\text{\AB{Γ} \entails{} \AIC{κ} \AB{k} \coentails{} \AB{Δ}}
}{ax}
\end{mathpar}
The introduction rule for tensor in the system with leftovers does
not involve partioning a multiset (a list in our implementation)
anymore: one starts by discharging the first subgoal, collects
the leftover from this computation, and then focuses on the second
one.
\begin{mathpar}
\inferrule{
     \text{\AB{Γ} \entails{} \AB{σ} \coentails{} \AB{Δ}}
\and \text{\AB{Δ} \entails{} \AB{τ} \coentails{} \AB{E}}
}{   \text{\AB{Γ} \entails{} \AB{σ} \tensor{} \AB{τ} \coentails{} \AB{E}}}
\end{mathpar}
The with type constructor on the other hand expects both
subgoals to be proven using the same resources. We formalise
this as the fact that both sides are proved using the input
context and that both leftovers are then synchronized.
Obviously, not all leftovers will be synchronizable: this
step may reject proof candidates which are non compatible.
\begin{mathpar}
\inferrule{
     \text{\AB{Γ} \entails{} \AB{σ} \coentails{} \AB{Δ₁}}
\and \text{\AB{Γ} \entails{} \AB{τ} \coentails{} \AB{Δ₂}}
\and \text{\AB{Δ} \eqsync{} \AB{Δ₁} \synced{} \AB{Δ₂}}
}{   \text{\AB{Γ} \entails{} \AB{σ} \with{} \AB{τ} \coentails{} \AB{Δ}}}
\end{mathpar}
We can now rewrite (see \autoref{fig:derivation}) the proof
described earlier in a fashion which distinguishes between
the state of the context before one starts proving a goal
and after it has been discharged entirely.
\begin{figure*}
\begin{mathpar}
\inferrule{
  \inferrule{
  }{\text{(\AB{σ} \tensor{} \AB{τ}) \with{} \AB{σ}
    \entails{} \AB{τ} \coentails{}
    (\AB{σ} \tensor{} \fba{\AB{τ}}) \with{} \AB{σ}}
  }{ax}
  \and
  \inferrule{
  }{\text{(\AB{σ} \tensor{} \fba{\AB{τ}}) \with{} \AB{σ}
    \entails{} \AB{σ} \coentails{}
    (\fba{\AB{σ}} \tensor{} \fba{\AB{τ}}) \with{} \AB{σ}}
  }{ax}
}{\text{(\AB{σ} \tensor{} \AB{τ}) \with{} \AB{σ}
        \entails{} \AB{τ} \tensor{} \AB{σ} \coentails{}
        \fbc{\fbb{(\fba{\AB{σ}} \tensor{} \fba{\AB{τ}})} \with{} \AB{σ}}}
}{\tensor{}^r}
\end{mathpar}
\caption{A proof with input / output contexts and usage
annotations\label{fig:derivation}}
\end{figure*}

It should not come as a suprise that this calculus does not
have any elimination rules for the various type constructors:
elimination rules do not consume anything, they merely shuffle
around (parts of) assumptions in the context and are, as a
consequence, not interesting proof steps. These are therefore
implicit in the process. This remark resonates a lot with
Andreoli's definition of focusing~\cite{andreoli1992logic}
whose goal was to prune the space search by declaring that the
logician does not care about the order in which some rules are
applied.

Ultimately, these rules being implicit is not an issue as
witnessed by the fact that the soundness result we give in
\autoref{sec:soundness} is constructive: we can mechanically
decide where to optimally insert the appropriate left rules
for the IMLL derivation to be correct.

\subsubsection{Computational interpretation}

Thinking of the derivation tree as the trace of a computation
(the proof search); we can notice that it is a monadic computation
that we are running. The axiom rule will introduce non-determinism;
they are indeed as many ways of proving an atomic proposition
as there assumptions of that type in the context. The rule for
tensor looks like two stateful operations being run sequentially:
one starts by discharging the first subgoal, waits for it to
\emph{return} a modified context and then uses these leftovers
to tackle the second one. And, last but not least, the rule for
tensor looks very much like a map-reduce diagram: we start by
generating two subcomputations which can be run in parallel and
later on merge their results by checking that the output contexts
are synchronized.

\section{Keeping the Structure\label{sec:contexts}}

We now have a calculus with input and output contexts; but
there is no material artefact describing the relationship
betwee these two. Sure, we could prove a lemma stating that
the leftovers are precisely the subset of the input context
which has not been used to discharge the goal but the proof
would be quite involved because, among other things, of the
merge operation hidden in the tensor rule.

But this is only difficult because we have forgotten the
structure of the problem and are still dealing with rather
extensional notions. Indeed, all of these intermediate
contexts are just \emph{the} one handed over to us when
starting the proof search procedure except that they come
with an usage annotation describing whether the various
assumptions are still available or have already been
consumed. This is the intuition we used in our example in
\autoref{example} when marking used atomic formulas with
a box \fba{ } rather than simply dropping them from the
context.

\subsection{Resource-Aware Contexts}

Let us make this all more formal. We start by defining
\AD{Cover}s: given a type \AB{σ}, a cover \AB{S} is a
formal object describing precisely which (non-empty) set of
parts of \AB{σ} have been consumed already. It is represented
by an inductive type listing all the different ways in which
a type may be partially used. The introduction rules, which
are listed in \autoref{fig:cover}, can be justified in the
following manner:
\begin{figure*}
\begin{mathpar}
\inferrule{
}{\text{\AIC{κ} \AB{k} \hasType{} \AD{Cover} \AIC{κ} \AB{k}}}
\and
\inferrule{
  \text{\AB{S} \hasType{} \AD{Cover} \AB{σ}}
  \and \text{\AB{T} \hasType{} \AD{Cover} \AB{τ}}
}{\text{\AB{S} \tensor{} \AB{T} \hasType{} \AD{Cover} \AB{σ} \tensor{} \AB{τ}}}
\and
\inferrule{\text{\AB{S} \hasType{} \AD{Cover} \AB{σ}}
}{\text{\AB{S} \tensor \free{τ} \hasType{} \AD{Cover} \AB{σ} \tensor{} \AB{τ}}}
\and
\inferrule{\text{\AB{T} \hasType{} \AD{Cover} \AB{τ}}
}{\text{\free{σ}\tensor{} \AB{T} \hasType{} \AD{Cover} \AB{σ} \tensor{} \AB{τ}}}
\end{mathpar}
\begin{mathpar}
\inferrule{ }{\text{\AB{σ} \with{} \AB{τ} \hasType{} \AD{Cover} \AB{σ} \with{} \AB{τ}}}
\and
\inferrule{\text{S \hasType{} \AD{Cover} \AB{σ}}
}{\text{\AB{S} \with\free{τ} \hasType{} \AD{Cover} \AB{σ} \with{} \AB{τ}}}
\and
\inferrule{\text{T \hasType{} \AD{Cover} \AB{τ}}
}{\text{\free{σ}\with{} \AB{T} \hasType{} \AD{Cover} \AB{σ} \with{} \AB{τ}}}
\end{mathpar}
\caption{The \AD{Cover} datatype\label{fig:cover}}
\end{figure*}
The cover for an atomic proposition can only be one thing:
the atom itself;

In the case of a tensor, both subtypes can be partially used
(cf. \AB{S} \tensor{} \AB{T}) or it may be the case that only
one side has been dug into so far (cf. \AB{S} \tensor \free{τ}
and \free{σ}\tensor{} \AB{T});

Similarly, a cover for a with-headed assumption can be a choice
of a side (cf. \AB{S} \with\free{τ} and \free{σ}\with{} \AB{T}).
Or, more surprisingly, it can be a full cover (cf. \AB{σ} \with{}
\AB{τ}) which is saying that \emph{both} sides will be entirely
used in different subtrees. This type of full cover is only ever
created when synchronizing two output contexts when using a with
introduction rule as in the following example:
\begin{mathpar}
\inferrule{
  \inferrule{ }{\text{\AB{σ} \with{} \AB{τ}
                \entails{} \AB{τ} \coentails{}
                \AB{σ} \with{} \fba{\AB{τ}}}}{ax}
  \and
  \inferrule{ }{\text{\AB{σ} \with{} \AB{τ}
                \entails{} \AB{σ} \coentails{}
                \fba{\AB{σ}} \with{} \AB{τ}}}{ax}
}{\text{\AB{σ} \with{} \AB{τ}
        \entails{} \AB{τ} \with{} \AB{σ} \coentails{}
        \fbb{\fba{\AB{σ}} \with{} \fba{\AB{τ}}}}}{\with{}^r}
\end{mathpar}

The \AD{Usage} of a type \AB{σ} is directly based on the idea
of a cover; it describes two different situations: either the
assumption has not been touched yet or it has been (partially)
used. Hence \AD{Usage} is the following datatype with two
constructors:
\begin{mathpar}
\inferrule{
}{\text{\AIC{[} \AB{σ} \AIC{]} \hasType{} \AD{Usage} \AB{σ}}
}
\and \inferrule{\text{\AB{pr} \hasType{} \AD{Cover} \AB{σ}}
}{\text{\AIC{]} \AB{pr} \AIC{[} \hasType{} \AD{Usage} \AB{σ}}
}
\end{mathpar}

Finally, we can extend the definition of \AD{Usage} to contexts
by a simple pointwise lifting. We call this lifting \AD{Usages}
to retain the connection between the two whilst avoiding any
ambiguities.
\begin{mathpar}
\inferrule{ }{\text{\AB{ε} \hasType{} \AD{Usages} \AIC{ε}}}
\and \inferrule{
     \text{\AB{Γ} \hasType{} \AD{Usages} \AB{γ}}
\and \text{\AB{S} \hasType{} \AD{Usage} \AB{σ}}
}{   \text{\AB{Γ} \mysnoc{} \AB{S} \hasType{} \AD{Usages} (\AB{γ} \mysnoc{} \AB{σ})}}
\end{mathpar}

\subsection{Being Synchronised, Formally}

Now that \AD{Usages} have been introduced, we can give a formal
treatment of the notion of synchronisation we evoked when giving
the with introduction rule for the calculus with leftovers.
Synchronization is a three place relation \AB{Δ} \eqsync{} \AB{Δ₁}
\synced{} \AB{Δ₂} defined as the pointwise lifting of an analogous
one working on \AD{Cover}s. Let us study the latter one which is
defined in an inductive manner.

It is reflexive which means that its diagonal \AB{S} \eqsync{} \AB{S}
\synced{} \AB{S} is always inhabited. For the sake of simplicty, we
do not add a constructor for reflexivity: this rule is admissible by
induction on \AB{S} based on the fact that synchronization for covers
comes with all the structural rule one would expect: if two covers'
root constructors are equal and their subcovers are synchronized then
it is only fair to say that both of them are synchronized.

It is also symmetric in its two last arguments which means that for
any \AB{Δ₁} and \AB{Δ₂}, if \AB{Δ} \eqsync{} \AB{Δ₁} \synced{} \AB{Δ₂}
then \AB{Δ} \eqsync{} \AB{Δ₂} \synced{} \AB{Δ₁}.

Synchronisation is not quite equality: subderivations may very-well
use different parts of a with-headed assumption without it being
problematic. Indeed: if both of these parts are \emph{entirely}
consumed then it simply means that we will  have to introduce a
different left rule at some point in each one of the subderivations.
This is the only point in the process where we may introduce the
cover \AB{σ} \with{} \AB{τ}. It can take place in different
situations:

The two subderivations may be using completely different parts of
the assumption:
\begin{mathpar}
\inferrule{\text{\isUsed{\AB{σ}}{\AB{S}}} \and \text{\isUsed{\AB{τ}}{\AB{T}}}
}{\text{\AB{σ} \with{} \AB{τ} \eqsync{} \AB{S} \with\free{\AB{τ}}
                              \synced{} \free{\AB{σ}}\with{} \AB{T}}
}
\end{mathpar}
But it may also be the case that only one of them is using only one
side of the \with{} whilst the other one is using both (e.g. think
of a proof of \AB{σ} \with{} \AB{τ} \entails{} \AB{σ} (\AB{σ} \with{} \AB{τ})):
\begin{mathpar}
\inferrule{\text{\isUsed{\AB{σ}}{\AB{S}}}
}{\text{\AB{σ} \with{} \AB{τ} \eqsync{} \AB{S} \with\free{\AB{τ}}
                              \synced{} \AB{σ} \with{} \AB{τ}}
}
\and
\inferrule{\text{\isUsed{\AB{τ}}{\AB{T}}}
}{\text{\AB{σ} \with{} \AB{τ} \eqsync{} \free{\AB{σ}}\with{} \AB{T}
                              \synced{} \AB{σ} \with{} \AB{τ}}
}
\end{mathpar}


\subsection{Resource-Aware Primitives}

Now that \AD{Usages} are properly defined, we can give a precise
type to our three place relations evoked before:

\begin{mathpar}
\inferrule{\text{\AB{Γ} \hasType{} \AD{Usages} \AB{γ}}
      \and \text{\AB{k} \hasType{} \AD{ℕ}}
      \and \text{\AB{Δ} \hasType{} \AD{Usages} \AB{γ}}
}{\text{\AB{Γ} \belongs{} \AB{k} \cobelongs{} \AB{Δ} \hasType{} \AP{Set}}
}
\and
\inferrule{\text{\AB{Γ} \hasType{} \AD{Usages} \AB{γ}}
      \and \text{\AB{σ} \hasType{} \AD{ty}}
      \and \text{\AB{Δ} \hasType{} \AD{Usages} \AB{γ}}
}{\text{\AB{Γ} \entails{} \AB{σ} \coentails{} \AB{Δ} \hasType{} \AP{Set}}
}
\end{mathpar}

The definition of the calculus has already be given before and
will not be changed. However we can at once define what it means
for a resource to be consumed in an axiom rule. \_\belongs{}\_\cobelongs{}\_
for \AD{Usages} is basically a proof-carrying de Bruijn index~\cite{de1972lambda}.
The proof is stored in the \AIC{zro} constructor and simply leverages
the definition of an anlogous \_\belongs{}\_\cobelongs{}\_ for \AD{Usage}.

\begin{mathpar}
\inferrule{\text{\AB{pr} \hasType{} \AB{S} \belongs{} \AB{k} \cobelongs{} \AB{S′}}
}{\text{\AIC{zro} \AB{pr} \hasType{} \AB{Γ} \mysnoc{} \AB{S}
        \belongs{} \AB{k} \cobelongs{}
        \AB{Γ} \mysnoc{} \AB{S′}}
}
\and
\inferrule{\text{\AB{pr} \hasType{} \AB{Γ} \belongs{} \AB{k} \cobelongs{} \AB{Δ}}
}{\text{\AIC{suc} \AB{pr} \hasType{} \AB{Γ} \mysnoc{} \AB{S}
        \belongs{} \AB{k} \cobelongs{}
        \AB{Δ} \mysnoc{} \AB{S}}
}
\end{mathpar}

The definition of \_\belongs{}\_\cobelongs{}\_ for \AD{Usage} is based
on two inductive types respectively describing what it means for a
resource to be consumed out of a mint assumption or out of an existing
cover.

\subsubsection{Consumption from a Mint Assumption}

We write \freebelongs{\AB{σ}} \AB{k} \cobelongs{} \AB{S} to mean that
by starting with a completely mint assumption of type \AB{σ}, we
consume \AB{k} and end up with the cover \AB{S} describing the leftovers.

In the case of an atomic formula there is only one solution: to use it
and end up with a total cover:
\begin{mathpar}
\inferrule{
}{\text{\freebelongs{\AIC{κ} \AB{k}} \AB{k} \cobelongs{} \AIC{κ} \AB{k}}
}
\end{mathpar}

In the case of with and tensor, one can decide to dig either in the left
or the right hand side of the assumption to find the right resource. This
give rise to four similarly built rules; we will only give one example:
going left on a tensor:
\begin{mathpar}
\inferrule{\text{\freebelongs{\AB{σ}} \AB{k} \cobelongs{} \AB{S}}
}{\text{\freebelongs{\AB{σ} \tensor{} \AB{τ}} \AB{k}
        \cobelongs{} \AB{S} \tensor\free{\AB{τ}}}
}
\end{mathpar}

\subsubsection{Consumption from an Existing Cover}

When we have an existing cover, the situation is slightly more
complicated. First, we can dig into an already partially used
sub-assumption using what we could call structural rules. All
of these are pretty similar so we will present only the one
harvesting the content on the left of a with type constructor:
\begin{mathpar}
\inferrule{\text{S \belongs{} \AB{k} \cobelongs{} \AB{S′}}
}{\text{S \with{} \AB{τ} \belongs{} \AB{k} \cobelongs{} \AB{S′} \with{} \AB{τ}}
}
\end{mathpar}
Second, we could invoke the rules defined in the previous paragraphs
to extract a resource from a sub-assumption that had been spared
so far. This can only affect tensor-headed assumption as covers for
with-headed ones imply that we have already picked a side and may not
using anything from the other one. Here is a such rule:
\begin{mathpar}
\inferrule{\text{\freebelongs{\AB{τ}} \AB{k} \cobelongs{} \AB{T}}
}{\text{S \tensor\free{\AB{τ}} \belongs{} \AB{k} \cobelongs{} \AB{S} \tensor{} \AB{T}}
}
\end{mathpar}

\section{Soundness\label{sec:soundness}}

The soundness result tells us that from a derivation in the more
general calculus, one can create a valid derivation in IMLL. To
be able to formulate such a statement, we need a way of listing
the assumptions which have been used in a proof \AB{Γ} \entails{}
\AB{σ} \coentails{} \AB{Δ}; informally, we should be able to describe
a usage \AB{E} such that \erasure{E} \entails{} \AB{σ}. To that effect,
we introduce the notion of difference between two usages.

\subsection{Usage Difference}

A usage difference \AB{E} between \AB{Γ} and \AB{Δ} (two elements of
type \AD{Usages} \AB{γ}) is a \AD{Usages} \AB{γ} such that \AB{Δ}
\eqsync{} \AB{Γ} \AD{─} \AB{E} holds where the three place relation
\_\eqsync{}\_\AD{─}\_ is defined as the pointwise lifting of a relation
on \AD{Usage}s itself based on a definition of cover differences.

Cover differences (\_\eqsync{}\_\diff{}\_) are defined by an
inductive type described (minus the expected structural laws which we
let the reader infer) in \autoref{fig:coverdiffs}.
\begin{figure*}[h]
\begin{mathpar}
\inferrule{ \text{\AB{S} \eqsync{} \AB{S₁} \diff{} \AB{S₂}}
}{\text{\AB{S} \tensor{} \AB{T} \eqsync{} \AB{S₁} \tensor{} \AB{T}
                                \diff{} \AB{S₂} \tensor\AIC{[} \AB{τ} \AIC{]}}
}
\and
\inferrule{ \text{\AB{S} \eqsync{} \AB{S₁} \diff{} \AB{S₂}}
}{\text{\AB{S} \tensor{} \AB{T} \eqsync{} \AB{S₁} \tensor\AIC{[} \AB{τ} \AIC{]}
                                \diff{} \AB{S₂} \tensor{} \AB{T}}
}
\end{mathpar}
\begin{mathpar}
\inferrule{ \text{\AB{T} \eqsync{} \AB{T₁} \diff{} \AB{T₂}}
}{\text{\AB{S} \tensor{} \AB{T} \eqsync{} \AB{S} \tensor{} \AB{T₁}
                                \diff{} \AIC{[} \AB{σ} \AIC{]}\tensor{} \AB{T₂}}
}
\and
\inferrule{\text{\AB{T} \eqsync{} \AB{T₁} \diff{} \AB{T₂}}
}{\text{\AB{S} \tensor{} \AB{T} \eqsync{} \AIC{[} \AB{σ} \AIC{]}\tensor{} \AB{T₁}
                                \diff{} \AB{S} \tensor{} \AB{T₂}}
}
\end{mathpar}
\begin{mathpar}
\inferrule{
}{\text{\AB{S} \tensor{} \AB{T} \eqsync{} \AIC{[} \AB{σ} \AIC{]}\tensor{} \AB{T}
                                \diff{} \AB{S} \tensor\AIC{[} \AB{τ} \AIC{]}}
}
\and
\inferrule{
}{\text{\AB{S} \tensor{} \AB{T} \eqsync{} \AB{S} \tensor\AIC{[} \AB{τ} \AIC{]}
                                \diff{} \AIC{[} \AB{σ} \AIC{]}\tensor{} \AB{T}}
}
\end{mathpar}
\caption{Cover differences\label{fig:coverdiffs}}
\end{figure*}



\begin{theorem}[Soundness of the Generalisation]
For all context \AB{γ}, all \AB{Γ}, \AB{Δ} of type \AD{Usages}
\AB{γ} and all goal \AB{σ} such that \AB{Γ} \entails{} \AB{σ}
\coentails{} \AB{Δ} holds, there exists an \AB{E} such that
\AB{Δ} \eqsync{} \AB{Γ} \AD{─} \AB{E} and \erasure{\AB{E}}
\entails{} \AB{σ}.
\end{theorem}
\begin{proof}
The proof is by induction on the derivation; using auxiliary
lemmas to combine the induction hypothesis.
\end{proof}

\begin{corollary}[Soundness of the Proof Search]
If the proof search shows that \AF{inj} \AB{γ} \entails{} \AB{σ}
\coentails{} \AB{Δ} holds for some \AB{Δ} and \AB{Δ} is a
complete usage then \AB{γ} \entails{} \AB{σ}.
\end{corollary}

The soundness result relating the new calculus to the original
one makes explicit the fact that valid IMLL derivations correspond
to the ones in the generalised calculus which have no leftovers.


\section{Search Parallelisation\label{sec:parallel}}

The reader familiar with linear logic will not have been surprised
by the fact that with is well-suited for a parallel exploration
of the provability of its sub-constituents. The algorithm we have
presented however remains sequential when it comes to a goal whose
head symbol is a tensor. But that is not a fatality: one can design
a tensor introduction rule which will let us try to produce both
subproofs in parallel. This is possible thanks to a check performed
a posteriori to make sure that the output contexts of the two
subcomputations are disjoint.
\begin{mathpar}
\inferrule{
     \text{\AB{Γ} \entails{} \AB{σ} \coentails{} \AB{Δ₁}}
\and \text{\AB{Γ} \entails{} \AB{τ} \coentails{} \AB{Δ₂}}
\and \text{\AB{Δ} \eqsync{} \AB{Δ₁} \disjoint{} \AB{Δ₂}}
}{   \text{\AB{Γ} \entails{} \AB{σ} \tensor{} \AB{τ} \coentails{} \AB{Δ}}}
\end{mathpar}
This approach would allow for a complete parallelisation of the
work at the cost of more subproofs being thrown away at the merge
stage because they do not fit together.

\section{Related work\label{sec:related}}

Andreoli's vastly influential work on focusing in Linear
Logic~\cite{andreoli1992logic} demonstrates that by using a more
structured calculus (the focused one), the logician can improve
her proof search procedure by making sure that she ignores irrelevant
variations between proof trees. The fact that our approach is based on
never applying a left rule explicitly and letting the soundness result
insert them in an optimal fashion is in the same vein: we are, effectively,
limiting the search space to proof trees with a very specific shape.

In the domain of certified proof search, Kokke and Swierstra
have designed a prolog-style procedure in Agda~\cite{kokkeauto}
which, using a fuel-based model, will explore a bounded part of
the set of trees describing the potential proofs generated by
backward-chaining with the goal as a starting point and a fixed
set of deduction rules as methods.

\bibliographystyle{alpha}
\bibliography{main}

\end{document}
