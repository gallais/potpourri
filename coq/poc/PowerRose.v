(*
This is code written while reading Appendix B of 
Nested Inductive Types
by Lamiaux, Forster, Sozeau, and Tabareau
https://hal.science/hal-05366368v1/
*)

(*
Power lists: the parameter is doubled in every tail.
*)

Inductive pList (a : Type) : Type :=
  | pnil : pList a
  | pcons : a -> pList (a * a) -> pList a.


(*
Predicate lifting for pList, so far so good
*)
Definition both {a : Type} (p : a -> Type) (v : (a * a)) : Type :=
  match v with
   (x, y) => (p x * p y)
  end.

Inductive allPList {a : Type} (p : a -> Type) : pList a -> Type :=
  | allPnil  : allPList p (pnil a)
  | allPcons : forall x xs,
      p x ->
      allPList (both p) xs ->
      allPList p (pcons a x xs).

(*
However we cannot form the inductive type!
*)
Fail Inductive pTree (a : Type) : Type :=
  | pLeaf : a -> pTree a
  | pNode : pList (pTree a) -> pTree a.

(*
code:
  - always 'start' to initialise the computation
  - one constructor per "pattern of modification", here we
    have one (pList (a * a)) so we just need to record "dup"

In this instance we have something that's essentially a nat, the
depth of the perfect tree of 'a's
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

(*
The predicate lifting for the containers obtained using `decode`
*)
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

Definition UnfoldDecode (a : Type) (c : code) : Type:=
  match c return Type with
    | start => a
    | dup c => (decode a c * decode a c)
  end.

Definition unfold_decode :
  forall a c, decode a c -> UnfoldDecode a c.
intros a c d; destruct d as [|c ds]; assumption.
Defined.

Definition fold_decode :
  forall a c, UnfoldDecode a c -> decode a c.
intros a [|] x; constructor; assumption.
Defined.


Definition fold_unfold_decode : forall a c (x : decode a c),
  x = fold_decode a c (unfold_decode a c x).
intros a c [|]; reflexivity.
Qed.

Definition map_both {a b : Type} (f : a -> b) (p : a * a) : (b * b) :=
  match p with (x, y) => (f x, f y) end.

Definition decode_both {a b : Type} {c : code} (f : decode a c -> b) (v : decode a (dup c)) : b * b.
  apply (map_both f); apply (unfold_decode _ (dup c)); assumption.
Defined.

Fixpoint gen_bpList_to_pList
  {a : Type} (c : code) (xs : bpList a c) {struct xs} :
  forall b, (decode a c -> b) -> pList b.
destruct xs as [|x xs]; intros b f.
  - apply pnil.
  - apply pcons.
    + exact (f x).
    + exact (gen_bpList_to_pList a (dup c) xs (b * b)%type (decode_both f)).
Defined.

Definition bpList_to_pList {a : Type} (xs : bpList a start) : pList a.
apply (gen_bpList_to_pList start xs).
exact (unfold_decode a start).
Defined.

(*
The corresponding predicate lifting.
*)

Inductive allBpList (a : Type) (p : a -> Type) (c : code) : bpList a c -> Type :=
  | allBpnil : allBpList a p c (bpnil a c)
  | allBpcons : forall x xs, allDecode p c x ->
    allBpList a p (dup c) xs -> allBpList a p c (bpcons a c x xs).


Definition gen_allBpList_to_PList
  {a : Type} (p : a -> Type) (c : code) {xs : bpList a c}
  (pxs : allBpList a p c xs) :
  forall b (f : decode a c -> b)
    (q : b -> Type) (pf : forall x, allDecode p c x -> q (f x)),
    allPList q (gen_bpList_to_pList c xs b f).
induction pxs as [|c x xs px pxs IHpxs]; intros b f q pf.
  - apply allPnil.
  - apply allPcons.
    + apply pf; assumption.
    + apply (IHpxs (b * b)%type (decode_both f) (both q)).
      intro d; rewrite (fold_unfold_decode _ _ d).
Admitted.

Definition allBpList_to_PList
  {a : Type} (p : a -> Type) (c : code) {xs : bpList a start}
  (pxs : allBpList a p start xs) : allPList p (bpList_to_pList xs).
apply gen_allBpList_to_PList with (p := p).
  - assumption.
  - intro x; rewrite (fold_unfold_decode _ _ x); simpl; inversion 1; subst; assumption.
Defined.

(* Power Trees:
  - Uses Barras' pList with the start code
*)

Inductive pTree (a : Type) : Type :=
  | pLeaf : a -> pTree a
  | pNode : bpList (pTree a) start -> pTree a.

(* TODO: induction by fixpoint *)

