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
Code:
  - always 'start' to initialise the computation
  - one constructor per "pattern of modification", here we
    have one (pList (a * a)) so we just need to record "dup"

In this instance we have something that's essentially a nat, the
depth of the perfect tree of 'a'
*)
Inductive Code : Type :=
  | start : Code
  | dup : Code -> Code.

(*
Decode:
  - essentially a function of the Code it is indexed by
  - expressed as a family to ensure strict positivity is noticed by Rocq
*)
Inductive Decode (a : Type) : Code -> Type :=
  | done : a -> Decode a start
  | pair : forall c, (Decode a c * Decode a c) -> Decode a (dup c).

(* Barras' pList:
  - instead of modifying the paremeter as we go, we record the
    modifications in the Code index
  - use Decode to deploy the modifications
*)
Inductive bpList (a : Type) (c : Code) : Type :=
  | bpnil : bpList a c
  | bpcons : Decode a c -> bpList a (dup c) -> bpList a c.

(* Power Trees:
  - Uses Barras' pList with the start Code
*)
Inductive pTree (a : Type) : Type :=
  | pLeaf : a -> pTree a
  | pNode : bpList (pTree a) start -> pTree a.

