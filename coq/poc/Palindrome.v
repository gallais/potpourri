(* Palindrome, from the middle *)

Require Import List.

Inductive PalAcc {A : Type} (acc : list A) : list A -> Type
  := Even : PalAcc acc acc
   | Odd  : forall x, PalAcc acc (x :: acc)
   | Step : forall x xs, PalAcc (x :: acc) xs -> PalAcc acc (x :: xs)
.

Definition Pal {A : Type} (xs : list A) : Type := PalAcc nil xs.

Theorem PalAccRevAcc {A : Type} (acc xs : list A) :
  PalAcc acc xs -> rev_append acc xs = rev_append xs acc.
Proof.
induction 1; trivial.
Qed.

Theorem PalRev {A : Type} (xs : list A) :
  Pal xs -> rev xs = xs.
Proof.
intro prf; rewrite rev_alt, <- (PalAccRevAcc _ _ prf); reflexivity.
Qed.

Theorem PalAccNext {A : Type} (acc xs : list A) x :
  PalAcc acc xs -> PalAcc (acc ++ (x :: nil)) (xs ++ (x :: nil)).
Proof.
induction 1; constructor; trivial.
Qed.


Theorem removelast_rev_append {A : Type} (acc xs : list A) :
  acc <> nil -> removelast (rev_append xs acc) = rev_append xs (removelast acc).
Proof.
revert acc; induction xs as [|a xs]; intros acc neq.
 - reflexivity.
 - simpl; destruct acc; [contradiction | apply IHxs; inversion 1].
Qed.

Theorem rev_append_cancel {A : Type} x (xs : list A) :
  x :: xs = rev xs ++ (x :: nil) -> { ys | xs = ys ++ (x :: nil) } + { xs = nil }.
Proof.
induction xs.
 - auto.
 - case_eq (rev (a :: xs)); [| intros y ys]; intros eq.
   + assert (Argh : a :: xs = nil).
     * rewrite <- (rev_involutive (a :: xs)), eq; reflexivity.
     * inversion Argh.
   + intro eq'; inversion eq'; eauto.
Qed.

Require Import PeanoNat.

Theorem RevPalAccStrong {A : Type} (n : nat) :
  forall (acc xs : list A), length xs <= n ->
  xs = rev xs -> PalAcc acc (xs ++ acc).
Proof.
induction n as [|n]; intros acc xs bnd eq.
 - destruct xs as [|a xs].
   + constructor.
   + destruct (Nat.nle_succ_0 _ bnd).
 - destruct xs as [|a xs].
   + constructor.
   + destruct (rev_append_cancel a xs eq) as [[ys prf]|prf]; subst.
     * simpl; constructor; rewrite <- app_assoc; simpl.
       apply IHn.
       -- etransitivity.
          eapply Nat.le_succ_diag_r.
          eapply Le.le_S_n.
          replace (S (S (length ys))) with (length (a :: ys ++ a :: nil)).
          ++ assumption.
          ++ simpl; rewrite app_length; simpl; rewrite Nat.add_1_r; reflexivity.
       -- simpl in eq; rewrite rev_app_distr in eq; simpl in eq.
          apply (f_equal (@tl _)) in eq; simpl in eq.
          apply app_inv_tail in eq.
          assumption.
     * constructor.
Qed.

Theorem RevPal {A : Type} (xs : list A) :
  xs = rev xs -> Pal xs.
Proof.
intro eq; unfold Pal; rewrite <- (app_nil_r xs);
 eapply RevPalAccStrong; trivial.
Qed.
