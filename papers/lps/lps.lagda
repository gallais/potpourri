\documentclass[preprint]{sigplanconf}
%\documentclass{article}
\usepackage{amsthm, amsmath}
\usepackage{mathpartir}
\usepackage[english]{babel}
\usepackage[references]{agda}
\usepackage{hyperref}

\usepackage{todonotes}

\usepackage{float}
\floatstyle{boxed}
\restylefloat{figure}

\setmainfont[Ligatures=TeX]{XITS}
\setmathfont{XITS Math}

\input{commands.tex}

\title{Certified Proof Search for Intuitionistic Linear Logic}

\authorinfo{ }
           { }
           { }

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{CONF 'yy}{Month d--d, 20yy, City, ST, Country} 
\copyrightyear{20yy} 
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm} 
\doi{nnnnnnn.nnnnnnn}


\maketitle

\begin{abstract}
In this article we show the difficulties a type-theorist
may face when attempting to formalise a decidability result
described informally. We then demonstrate how generalising
the problem and switching to a more structured presentation
can alleviate her suffering.

The calculus we target is a fragment of Intuitionistic
Linear Logic (ILL onwards) and the tool we use to construct
the search procedure is Agda (but any reasonable type theory
equipped with data types could do). We believe the approach
described here can be used in other settings.
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
working on a fragment of ILL~\cite{girard1987linear}, the sort
of pitfalls to avoid and the generic ideas leading to better-behaved
formulations.
In \autoref{sec:ILL} we describe the fragment of ILL we are
studying; \autoref{sec:general} defines a more general calculus
internalising the notion of leftovers and \autoref{sec:contexts}
introduces resource-aware contexts thus giving us a powerful
language to target with our proof search algorithm. The soudness
result proved in \autoref{sec:soundness} is what lets us recover
an ILL proof from one expressed in the more general system.


\section{The Calculus, Informally\label{sec:ILL}}

The calculus we are considering is a fragment of Intuitionistic
Multiplicative Linear Logic composed of countably many \textit{atomic}
types, \textit{tensor} products and \textit{with}. This is summed
up by the following grammar for types:

$$
\text{\AD{ty} ~∷=~ \AIC{κ} \AD{ℕ} ~|~ \AD{ty} \tensor{} \AD{ty}
                                  ~|~ \AD{ty} \with{} \AD{ty}}
$$

The calculus' sequents (\AB{Γ} \entails{} \AB{σ}) are composed of
a multiset of types (\AB{Γ}) describing the resources available in
the context and a type (\AB{σ}) corresponding to the proposition
one is trying to prove. Each type constructor comes with both
introduction and elimination rules (also known as, repesctively,
right and left rules because of the side of the sequent they affect)
described in \autoref{fig:ILLRules}. Multisets are intrinsically
extensional hence the lack of a permutation rule one may be used to
seeing in various list-based presentations.
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
\caption{Introduction and Elimination rules for ILL\label{fig:ILLRules}}
\end{figure*}

However these rules are from algorithmic: the logician needs to
\emph{guess} when to apply an elimination rule or which partition
to pick when introducing a tensor. This makes this calculus really
ill-designed for her to perform a proof search in a sensible manner.

So, rather than sticking to the original presentation and trying
to work around the inconvenience of dealing with rules which are
not algorithmic, and intrinsically extensional notions such as the
one of multisets, it is possible to generalise the calculus in order
to have a more palatable formal treatment.

The principal insight in this development is that proof search in
Linear Logic is not just about fully using the context provided to
us as an input in order to discharge a goal. The bulk of the work
is rather to use parts of some of the assumptions in a context to
discharge a first subgoal; collect the leftovers and invest them
into trying to discharge another subproblem. Only in the end should
the leftovers be down to nothing.

This observation leads to the definition of two new notions: first,
the calculus is generalized to one incorporating the notion of
leftovers; second, the contexts are made resource-aware meaning
that they keep the same structure whilst tracking whether (parts
of) an assumption has been used already. Proof search becomes
consumption annotation.

\section{Generalising the Problem\label{sec:general}}

 In this section, we will start by studying a
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

The goal's head symbol is a \tensor{}; as we have no interest
in guessing whether to apply left rules or how to partition
the current context ─if at all necessary─, we are simply going
to start by looking for a proof of its left part. Given that
\AB{τ} is an atomic formula, the only way to discharge this goal
is to use an assumption available in the context. Luckily for
us, there is a \AB{τ} in the context; we are therefore able to
produce the following derivation:
\begin{mathpar}
\inferrule{
}{\text{(\AB{σ} \tensor{} \fba{\AB{τ}}) \with{} \AB{σ} \entails{} \AB{τ}}
}{ax}
\end{mathpar}
Now that we are done with the left subgoal, we can deal with
the right one. The main difference is that our available context
is not (\AB{σ} \tensor{} \AB{τ}) \with{} \AB{σ} anymore but
rather the consumption annotated (\AB{σ} \tensor{} \fba{\AB{τ}}) \with{} \AB{σ}.
We are once more facing an atomic formula which we can only
discharge by using an assumption. This time there are two
candidates in the context except that one of them is inaccessible:
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
tells us that this translates into a valid ILL proof tree. And
it is indeed the case: by following the structure of the pseudo-proof
we just generated above and adding the required left rules\footnote{We
will explain in \autoref{sec:soundness} how deciding where these left
rules should go can be done automatically.}, we get the following
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
internalised. When we write down the sequent \AB{Γ} \entails{}
\AB{σ} \coentails{} \AB{Δ}, we mean that from the input \AB{Γ},
we can prove \AB{σ} with leftovers \AB{Δ}. Let us see what a
linear calculus would look like in this setting.

If we assume that we already have in our possession a similar relation
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
the leftover from this computation, and then deals with the second
one. 
\begin{mathpar}
\inferrule{
     \text{\AB{Γ} \entails{} \AB{σ} \coentails{} \AB{Δ}}
\and \text{\AB{Δ} \entails{} \AB{τ} \coentails{} \AB{E}}
}{   \text{\AB{Γ} \entails{} \AB{σ} \tensor{} \AB{τ} \coentails{} \AB{E}}}
\end{mathpar}
This is a left-skewed presentation but could just as well be a
right-skewed one. We also discuss (in \autoref{sec:parallel}) the
opportunity for parallelisation of the proof search a symmetric
version could offer as well as the additional costs it would
generate.

The with type constructor on the other hand expects both
subgoals to be proven using the same resources. We formalise
this as the fact that both sides are proved using the input
context and that both leftovers are then synchronized (for a
sensible, yet to be defined, definition of synchronisation).
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
have any elimination rule for the various type constructors:
elimination rules do not consume anything, they merely shuffle
around (parts of) assumptions in the context and are, as a
consequence, not interesting proof steps. These are therefore
implicit in the process. This remark resonates a lot with
Andreoli's definition of focusing~\cite{andreoli1992logic}
whose goal was to prune the search space by declaring that the
logician does not care about the order in which some commuting
rules are applied.

Ultimately, these rules being implicit is not an issue as
witnessed by the fact that the soundness result we give in
\autoref{sec:soundness} is constructive: we can mechanically
decide where to optimally insert the appropriate left rules
for the ILL derivation to be correct.

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
with looks very much like a map-reduce diagram: we start by
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
parts of \AB{σ} has been consumed already. The set of covers
of a type \AB{σ} is represented by an inductive family \AD{Cover}
\AB{σ} listing all the different ways in which \AB{σ} may be
partially used. The introduction rules, which are listed
in \autoref{fig:cover}, can be justified in the following
manner:
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
created when synchronising two output contexts by using a with
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
        \fba{\AB{σ} \with{} \AB{τ}}}}{\with{}^r}
\end{mathpar}
The \AD{Usage} of a type \AB{σ} is directly based on the idea
of a cover; it describes two different situations: either the
assumption has not been touched yet or it has been (partially)
used. Hence \AD{Usage} is the following datatype with two infix
constructors\footnote{The way the brackets are used is meant to
convey the idea that \AIC{[} \AB{σ} \AIC{]} is in mint condition
whilst \AIC{]} \AB{S} \AIC{[} is dented.}:
\begin{mathpar}
\inferrule{
}{\text{\AIC{[} \AB{σ} \AIC{]} \hasType{} \AD{Usage} \AB{σ}}
}
\and \inferrule{\text{\AB{S} \hasType{} \AD{Cover} \AB{σ}}
}{\text{\AIC{]} \AB{S} \AIC{[} \hasType{} \AD{Usage} \AB{σ}}
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
}{   \text{\AB{Γ} \mysnoc{} \AB{S} \hasType{} \AD{Usages} \AB{γ} \mysnoc{} \AB{σ}}}
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
comes with all the structural rules one would expect: if two covers'
root constructors are equal and their subcovers are synchronized then
it is only fair to say that both of them are synchronised.

It is also symmetric in its two last arguments which means that for
any \AB{Δ}, \AB{Δ₁}, and \AB{Δ₂}, if \AB{Δ} \eqsync{} \AB{Δ₁} \synced{} \AB{Δ₂}
holds then so does \AB{Δ} \eqsync{} \AB{Δ₂} \synced{} \AB{Δ₁}.

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
side of the \with{} whilst the other one is a full cover
(see \autoref{fig:fullcov} for an example):
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
\begin{figure*}
\begin{mathpar}
\inferrule*[Right=\with{}$^r$]{
  \inferrule*[Right=\textit{ax}]{
    }{\text{\AB{σ} \with{} \AB{τ}
            \entails{} \AB{σ}
            \coentails{} \fba{\AB{σ}} \with{} \AB{τ}}
    }
  \and
  \inferrule*[Right=\with{}$^r$]{
    \inferrule*[Right=\textit{ax}]{
      }{\text{\AB{σ} \with{} \AB{τ}
              \entails{} \AB{σ}
              \coentails{} \fba{\AB{σ}} \with{} \AB{τ}}
      }
    \and
    \inferrule*[Right=\textit{ax}]{
      }{\text{\AB{σ} \with{} \AB{τ}
              \entails{} \AB{τ}
              \coentails{} \AB{σ} \with{} \fba{\AB{τ}}}
      }
    \and \text{\fba{\AB{σ} \with{} \AB{τ}}
               \eqsync{} \fba{\AB{σ}} \with{} \AB{τ}
               \synced{} \AB{σ} \with{} \fba{\AB{τ}}}
    }{\text{\AB{σ} \with{} \AB{τ}
            \entails{} \AB{σ} \with{} \AB{τ}
            \coentails{} \fba{\AB{σ} \with{} \AB{τ}}}
    }
  \and \text{\fba{\AB{σ} \with{} \AB{τ}}
             \eqsync{} \fba{\AB{σ}} \with{} \AB{τ}
             \synced{} \fba{\AB{σ} \with{} \AB{τ}}}
}{\text{\AB{σ} \with{} \AB{τ}
        \entails{} \AB{σ} \with{} (\AB{σ} \with{} \AB{τ})
        \coentails{} \fba{\AB{σ} \with{} \AB{τ}}}
}
\end{mathpar}
\caption{A derivation with a synchronisation combining a
        left cover of a with together with a full one.\label{fig:fullcov}}
\end{figure*}

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

The definition of the calculus has already been given before and
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

\section{Proof Search}

We have defined a lot of elegant datatypes so far but the original
goal was to implement a proof search algorithm for the fragment of
ILL we have decided to study. The good news is that all the systems
we have described have algorithmic rules: read bottom-up, they are
a set of constructor-directed recipes to search for a proof. Depending
on the set of rules, they may or may not be deterministic and they
clearly are not total because not all sequents are provable. This
simply means that we will be working in various monads: the list one
to model non determinism and the maybe one to model partiality.

Now, the presence of these effects is a major reason why it is important
to have the elegant intermediate structures we can generate inhabitants
of. Even if we are only interested in the satisfiability of a given problem,
having material artefacts at our disposal allows us to state and prove
properties of these functions easily rather than suffering from boolean
blindness.\todo{cite a paper (?) on Boolean Blindness}.
And we know that we should be able to optimise them
away~\cite{wadler1990deforestation, gill1993short} in the case where
we are indeed only interested in the satisfiability of the problem.

\subsection{Consuming an Atomic Proposition}

The proof search procedures are rather simple to implement (they simply
follow the specifications we have spelled out earlier) and their definitions
are succinct. For instance, the decision procedure for
\_\belongs{}\_\cobelongs{}\_ is made up of four functions totalling 18 lines
of code, including a toplevel type annotation for each one of them. Let us
study them.

\AgdaHide{
\begin{code}
module lps where

open import Data.Nat
open import Data.Product as Product hiding (map)
open import Function

open import lps.IMLL
open Type
open import lps.Search.Calculus
open Calculus hiding (_⊢?_)
open import lps.Search.BelongsTo as BelongsTo
open BelongsTo.Context hiding (_∋_∈_)
open BelongsTo.Type.Cover.FromFree hiding (_∈?[_])
open BelongsTo.Type.Cover.FromDented hiding (_∈?_)
open import lps.Linearity
open LC
open LT hiding (Usage)

open import lps.Linearity.Action as Action
open Action.Context

open import lib.Nullary
open import lib.Maybe
open import lib.Context as Con
open Con.Context
open Con.Context.Context

pattern ax  k          = `κ k
pattern _⊗ʳ_ a b       = _`⊗ʳ_ a b
pattern _&ʳ_by_ a b pr = _`&ʳ_by_ a b pr

pattern [] = ε

pattern κ   k   = `κ k
pattern _⊗[_] a b = a `⊗[ b ]
pattern [_]⊗_ a b = [ a ]`⊗ b
pattern _⊗_ a b = a `⊗ b
pattern _&_ a b = a `& b
\end{code}
}

\begin{lemma}Given a type \AB{σ}, we can decide whether it is possible
to consume an atomic proposition \AB{k} from the corresponding mint
assumption.
\end{lemma}
\begin{proof}We write \AF{\_∈?[\_]} for the function describing the
different ways in which one can consume an assumption from a mint
assumption. This function, working in the list monad, is defined by
structural induction on its second (explicit) argument: the mint
assumption's type.

\AgdaHide{
\begin{code}
_∈?[_] : (k : ℕ) (σ : ty) → Con (Σ[ S′ ∈ Cover σ ] [ σ ]∋ k ∈ S′)
\end{code}}

\underline{Atomic Case} If the mint assumption is just an atomic
proposition then it may be used if and only if it is the same
proposition. Luckily this is decidable; in the case where propositions
are indeed equal, we return the corresponding consumption whilst we
simply output the empty list otherwise.

\begin{code}
k ∈?[ κ l   ] = dec (k ≟ l) (return ∘ ∈κ k) (const [])
\end{code}

\underline{Tensor \& With Case} Both the tensor and with case amount
to picking a side. Both are equally valid so we just concatenate the
lists of potential proofs after having mapped function inserting the
right constructors to record the choices we have made on each side.

\begin{code}
k ∈?[ σ ⊗ τ ]  =   map (∈[⊗]ˡ τ)  (k ∈?[ σ ])
               ++  map (∈[⊗]ʳ σ)  (k ∈?[ τ ])
k ∈?[ σ & τ ]  =   map (∈[&]ˡ τ)  (k ∈?[ σ ])
               ++  map (∈[&]ʳ σ)  (k ∈?[ τ ])
\end{code}
\end{proof}

\begin{lemma}Given a cover \AB{S}, we can decide whether it is possible
to extract and consume an atomic proposition \AB{k} from it.
\end{lemma}
\begin{proof}We write \AF{\_∈?]\_[} for the function describing the
different ways in which one can consume an assumption from an already
existing cover. This function, working in the list monad, is defined
by structural induction on its second (explicit) argument: the cover.
\AgdaHide{
\begin{code}
_∈?]_[ : (k : ℕ) {σ : ty} (S : Cover σ) → Con (Σ[ S′ ∈ Cover σ ] S ∋ k ∈ S′)
\end{code}}

\underline{Atomic Case} The atomic proposition has already been used,
there is therefore no potential proof:

\begin{code}
k ∈?] κ l      [ = []
\end{code}

\underline{Tensor Cases} The tensor cases all amount to collecting
all the ways in which one may use the sub-assumptions. Whenever a
sub-assumption is already partially used (in other words: a \AD{Cover})
we use the induction hypothesis delivered by the function \AF{\_∈?]\_[};
if it is mint then we can fall back to the previous lemma. In each case,
we then map lemmas applying the appropriate rules recording the choices
made.

\begin{code}
k ∈?] A ⊗ B     [  =   map (∈⊗ˡ B)    (k ∈?] A [)
                   ++  map (∈⊗ʳ A)    (k ∈?] B [)
k ∈?] [ a ]⊗ B  [  =   map (∈[]⊗ˡ B)  (k ∈?[ a ])
                   ++  map (∈[]⊗ a)   (k ∈?] B [)
k ∈?] A ⊗[ b ]  [  =   map (∈⊗[] b)   (k ∈?] A [)
                   ++  map (∈⊗[]ʳ A)  (k ∈?[ b ])
\end{code}

\underline{With Cases} Covers for with are a bit special: either
they are stating that an assumption has been fully used (meaning
that there is no way we can extract the atomic proposition \AB{k}
out of it) or a side has already been picked and we can only
explore one sub-assumption.

\begin{code}
k ∈?] a & b       [ = []
k ∈?] A `&[ b ]   [ = map (∈&[] b)  (k ∈?] A [)
k ∈?] [ a ]`& B   [ = map (∈[]& a)  (k ∈?] B [)
\end{code}
\end{proof}

Now that we know how to list the ways in which one can extract and
consume an atomic proposition from a mint assumption or an already
existing cover, it is trivial to define the corresponding process
for an \AD{Usage} by calling the appropriate function.

\begin{corollary}Given an \AB{S} of type \AD{Usage} \AB{σ} and an atomic
proposition \AB{k}, one can produce a list of pairs consisting of a
\AD{Usage} \AB{σ} we will call \AB{T} and a proof that
\AB{S} \belongs{} \AB{k} \cobelongs{} \AB{T}.
\end{corollary}

This leads us to the theorem describing how to implement proof
search for the \_\belongs{}\_\cobelongs{}\_ relation used in
the axiom rule.

\begin{theorem}Given a \AB{Γ} of type \AD{Usages} \AB{γ} and an atomic
proposition \AB{k}, one can produce a list of pairs consisting of a
\AD{Usages} \AB{γ} we will call \AB{Δ} and a proof that
\AB{Γ} \belongs{} \AB{k} \cobelongs{} \AB{Δ}.
\end{theorem}
\begin{proof}We simply apply the function described in the previous
corollary to each one of the assumption in the context and collect
all of the possible solutions.
\end{proof}


\subsection{Producing Derivations}

\begin{theorem}[Proof Search] Given an \AB{S} of type \AD{Usage} \AB{σ}
and a type \AB{σ}, it is possible to produce a list of pairs consisting
of a \AD{Usage} \AB{σ} we will call \AB{T} and a proof that
\AB{S} \entails{} \AB{k} \coentails{} \AB{T}.
\end{theorem}
\begin{proof} We write \AF{\_⊢?\_} for this function. It is defined by
structural induction on its second (explicit) argument: the goal's type.
We work, the whole time, in the list monad.

\AgdaHide{
\begin{code}
infix 1 _⊢?_
_⊢?_ : ∀ {γ : Con ty} (Γ : Usage γ) (σ : ty) → Con (Σ[ Δ ∈ Usage γ ] Γ ⊢ σ ⊣ Δ)

whenSome : ∀ {γ : Con ty} {Γ : Usage γ} {Δ₁ Δ₂ : Usage γ}
             {σ τ : ty} → Γ ⊢ σ ⊣ Δ₁ → Γ ⊢ τ ⊣ Δ₂ →
             Σ[ Δ ∈ Usage γ ] Δ ≡ Δ₁ ⊙ Δ₂ →
             Con (Σ[ Δ ∈ Usage γ ] Γ ⊢ σ & τ ⊣ Δ)
\end{code}}
\AgdaHide{
%<*whenSomeCode>
\begin{code}
whenSome prσ prτ (Δ , pr) = return $ Δ , prσ &ʳ prτ by pr
\end{code}
%</whenSomeCode>
}

\underline{Atomic Case} Trying to prove an atomic proposition amounts to
lifting the various possibilities provided to us by \AF{\_∈?\_} thanks to
the axiom rule \AF{ax}.

\begin{code}
Γ ⊢? κ k =  map (Product.map id ax) $ k ∈? Γ
\end{code}

\underline{Tensor Case} After collecting the leftovers for each potential
proof of the first subgoal, we try to produce a proof of the second one.
If both of these phases were successful, we can then combine them with the
appropriate tree constructor \AD{⊗ʳ}.

\begin{code}
Γ ⊢? σ ⊗ τ  =  Γ  ⊢? σ >>= uncurry $ λ Δ prσ →
               Δ  ⊢? τ >>= uncurry $ λ E prτ →
               return $ E , prσ ⊗ʳ prτ
\end{code}

\underline{With Case} Here we produce two independent sets of potential
proofs and then check which subset of their cartesian product gives rise
to valid proofs. \AF{\_⊙?\_} checks whether two \AD{Usages} are in sync;
if they are then we return a derivation and otherwise we just output the
empty list.

\begin{code}
Γ ⊢? σ & τ  =  Γ ⊢? σ >>= uncurry $ λ Δ₁ prσ →
               Γ ⊢? τ >>= uncurry $ λ Δ₂ prτ →
               maybe (whenSome prσ prτ) [] $ Δ₁ ⊙? Δ₂
\end{code}

Where \AF{whenSome} is defined in the following manner:

\ExecuteMetaData[lps.tex]{whenSomeCode}

\end{proof}

\section{Soundness\label{sec:soundness}}

The soundness result tells us that from a derivation in the more
general calculus, one can create a valid derivation in ILL. To
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
\todo{Usage constructors}

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
one makes explicit the fact that valid ILL derivations correspond
to the ones in the generalised calculus which have no leftovers.


\section{Related and Future Work\label{sec:related}}

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

\subsection{Tackling a Larger Fragment}

The fragment we are studying is non trivial: having only tensor
and atomic formulas would be equivalent to testing bag equality
between the context and the goal; and limiting ourselves to with
and atomic formulas would amount to checking that there is a
non-empty intersection between the context and the goal. However
mixing tensors and withs creates a more intricate theory hence
this whole development.

A very important connector in ILL is the lollipop. Although dealing
with it on the right hand side is extremely simple (one just extends
the context with the newly acquired assumption and check that it has
been entirely consumed in the subderivation corresponding to the body
of the lambda abstraction), its elimination rule is more complex: if
\AB{σ} \lolli{} \AB{τ} belongs to the context, then one needs to be
able to make this specific assumption temporarily unavailable when
proving its premise. Indeed, it would otherwise be possible to use its
own body to discharge the premise thus leading to a strange fixpoint
making e.g. \AB{σ} \lolli{} (\AB{σ} \tensor{} \AB{σ}) \entails{} \AB{σ}
provable. A well-structured solution has yet to be found.


\subsection{Search Parallelisation\label{sec:parallel}}

The reader familiar with linear logic will not have been surprised
by the fact that with is well-suited for a parallel exploration
of the provability of its sub-constituents. The algorithm we have
presented however remains sequential when it comes to a goal whose
head symbol is a tensor. But that is not a fatality: it is possible
to design a tensor introduction rule following the map-reduce approach
seen earlier. It will let us try to produce both subproofs in parallel
before performing an \textit{a posteriori} check to make sure that the
output contexts of the two subcomputations are disjoint.
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

\section*{Special Thanks}

This paper was typeset thanks to Stevan Andjelkovic's work to make
compilation from literate agda to latex possible.

\bibliographystyle{alpha}
\bibliography{main}

\end{document}
