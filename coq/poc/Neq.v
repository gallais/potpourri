From Equations Require Import Equations.

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

Theorem Neq_is_neq : forall {t1 t2}, Neq t1 t2 -> t1 <> t2.
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

Instance eq_dec : EqDec.EqDec BTree.
Proof.
intros t1 t2; destruct (eq_or_Neq t1 t2);
 now (constructor; try (apply Neq_is_neq); assumption).
Qed.

Theorem LeafNode_pi : forall l r (p : Neq Leaf (Node l r)), p = LeafNode l r.
intros l r p; dependent induction p; inversion H; subst.
apply EqDec.inj_right_sigma in H; assumption.
Qed.

Theorem NodeLeaf_pi : forall l r (p : Neq (Node l r) Leaf), p = NodeLeaf l r.
intros l r p; dependent induction p; inversion H; subst.
apply EqDec.inj_right_sigma in H; assumption.
Qed.

Theorem NodeNode_inversion : forall {l1 r1 l2 r2} (p : Neq (Node l1 r1) (Node l2 r2)),
  { q : Neq l1 l2 | p = NodeLeft l1 l2 r1 r2 q }
  + { eq : l1 = l2 & { q : Neq r1 r2 | p = NodeRight l1 l2 r1 r2 eq q } }.
intros l1 r1 l2 r2 p; dependent induction p; inversion H; subst.
  all: apply EqDec.inj_right_sigma in H; now (constructor; repeat eexists; eassumption).
Qed.

Theorem Neq_pi : forall t1 t2 (p q : Neq t1 t2), p = q.
Proof.
intros t1 t2 p; induction p; intro q.
  + symmetry; apply LeafNode_pi.
  + symmetry; apply NodeLeaf_pi.
  + destruct (NodeNode_inversion q) as [[p0 eqn] | [eq [_ _]]].
    * rewrite (IHp p0); symmetry; assumption.
    * assert (argh := Neq_is_neq p); contradiction.
  + destruct (NodeNode_inversion q) as [[p0 _] | [eq [p0 eqn]]].
    * assert (argh := Neq_is_neq p0); contradiction.
    * rewrite (IHp p0), (UIP BTree l1 l2 e eq); symmetry; assumption.
Qed.
