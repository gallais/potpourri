(*
This is code written while reading Appendix B of 
Nested Inductive Types
by Lamiaux, Forster, Sozeau, and Tabareau
https://hal.science/hal-05366368v1/
*)

Inductive pList (a : Type) : Type :=
  | pnil : pList a
  | pcons : a -> pList (a * a) -> pList a.

(*
code:
  - always 'start' to initialise the computation
  - one constructor per "pattern of modification", here we
    have one (pList (a * a)) so we just need to record "dup"

In this instance we have something that's essentially a nat, the
depth of the perfect tree of 'a'
*)
Inductive code : Type :=
  | start : code
  | dup : code -> code.

(*
decode:
  - essentially a function of the code it is indexed by
  - expressed as a family to ensure strict positivity is noticed by Rocq
*)
Inductive decode (a : Type) : code -> Type :=
  | done : a -> decode a start
  | pair : forall c, (decode a c * decode a c) -> decode a (dup c).

Inductive allDecode {a : Type} (p : a -> Type) : forall c, decode a c -> Type :=
  | allDone : forall x, p x -> allDecode p start (done a x)
  | allPair : forall c l r,
     (allDecode p c l * allDecode p c r) ->
     allDecode p (dup c) (pair a c (l, r)).

(* Barras' pList:
  - instead of modifying the paremeter as we go, we record the
    modifications in the code index
  - use decode to deploy the modifications
*)
Inductive bpList (a : Type) (c : code) : Type :=
  | bpnil : bpList a c
  | bpcons : decode a c -> bpList a (dup c) -> bpList a c.

Inductive allBpList (a : Type) (p : a -> Type) (c : code) : bpList a c -> Type :=
  | allBpnil : allBpList a p c (bpnil a c)
  | allBpcons : forall x xs, allDecode p c x ->
    allBpList a p (dup c) xs -> allBpList a p c (bpcons a c x xs).

(* Power Trees:
  - Uses Barras' pList with the start code
*)
Inductive pTree (a : Type) : Type :=
  | pLeaf : a -> pTree a
  | pNode : bpList (pTree a) start -> pTree a.

(* TODO: induction by fixpoint *)