Inductive BTree : Type
  := Leaf
   | Node : BTree -> BTree -> BTree.

Inductive Neq : BTree -> BTree -> Set
  (* Constructor mismatch *)
  := LeafNode  : forall l r, Neq Leaf (Node l r)
   | NodeLeaf  : forall l r, Neq (Node l r) Leaf
  (* (Equal) clowns to the Left, Jokers to the right *)
   | NodeLeft  : forall l1 l2 r1 r2, Neq l1 l2 -> Neq (Node l1 r1) (Node l2 r2)
   | NodeRight : forall l1 l2 r1 r2, l1 = l2 -> Neq r1 r2 -> Neq (Node l1 r1) (Node l2 r2)
   .

Theorem Neq_is_neq : forall t1 t2, Neq t1 t2 -> t1 <> t2.
Proof.
intros t1 t2; induction 1; inversion 1; contradiction.
Qed.

Theorem eq_or_Neq : forall t1 t2, (t1 = t2) + Neq t1 t2.
Proof.
intro t1; induction t1 as [| l1 IHl1 r1 IHr1]; intros [|l2 r2].
  all: try (now (do 2 constructor)).
  destruct (IHl1 l2); subst.
  + destruct (IHr1 r2); subst.
    * left; reflexivity.
    * now (right; constructor; trivial).
  + now (right; constructor; trivial).
Qed.

Theorem eq_dec : forall (t1 t2 : BTree), { t1 = t2 } + { t1 <> t2 }.
Proof.
intros t1 t2; destruct (eq_or_Neq t1 t2);
 now (constructor; try (apply Neq_is_neq); assumption).
Qed.


(*
Theorem leafNode_pi : forall l r (p : Neq Leaf (Node l r)), p = LeafNode l r.
intros l r p; dependent induction p; reflexivity.
Qed.

Print Assumptions leafNode_pi.

Theorem Neq_pi : forall t1 t2 (p q : Neq t1 t2), p = q.
Proof.
intros t1 t2 p; induction p; intro q; dependent induction q.
*)