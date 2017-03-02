(* Coq tactics, ready to be copy-pasted into your current project.
 *)


(* Breaks an exsistential quantifier out into it's pieces *)
Ltac break_step H :=
  match type of H with
  (exists x, _) =>
    let x' := fresh x in
    destruct H as [x H]
  end.

Ltac break H :=
  repeat (break_step H).

Example break_unit :
  (exists a b, a /\ b)
  -> (exists a b, a /\ b)
  -> (exists a b, a \/ b).
Proof.
  intros Hab Hab2.
  break Hab.
  exists a, b.
  destruct Hab as [Ha Hb].
  left; assumption.
Qed.


(** refl:
Because I can't spell reflexivity.
 **)

Ltac refl_step :=
  match goal with
    (* if it works, it works *)
  | |- _ => reflexivity
  | |- _ = _ => assumption
    (* clear the H after use make sure that no infinite
       recursion happens *)
  | [ H : _ = _ |- _ ] =>
    rewrite <- H; clear H
  | [ H : _ = _ |- _ ] =>
    rewrite -> H; clear H
  end.

Ltac refl :=
  (* define refl to repeat until success, or fail *)
  repeat refl_step; fail.

Example refl_unit :
  forall a, a = 1 -> a = 1.
Proof.
  intros a Ha.
  refl.
Qed.

Example refl_rev_unit :
  forall a, 1 = a -> a = 1.
Proof.
  intros a Ha.
  refl.
Qed.

Example refl_trans_unit :
  forall a b c : Type, a = b -> b = c -> a = c.
Proof.
  intros a b c Hab Hbc.
  refl.
Qed.

(** UNROLL **)

Require Import List.
Import ListNotations.

(* Try to prove that something is not in a list*)
Ltac unroll_false_step H :=
  match type of H with
  | In _ _ =>
    unfold In in H
  | _ \/ _ =>
    destruct H as [H | H]
  | _ = _ =>
    discriminate
  | False =>
    destruct H
  end.

Tactic Notation "unroll" "in" hyp(H) :=
  repeat (unroll_false_step H).

Example unroll_false_unit:
  ~ In 4 [1; 2; 3].
Proof.
  intros H.
  unroll in H.
Qed.

(* Try to prove that something is in a list *)
Ltac unroll_step :=
  match goal with
  | |- ~ In _ _ =>
    let H := fresh "Hunroll" in
    intro H; unroll in H
  | |- In _ _ =>
    unfold In
  | |- _ \/ _  => left; refl
  | |- _ \/ _  => right
  end.

Ltac unroll := repeat unroll_step.

Example unroll_not_unit:
  ~ In 4 [1; 2; 3].
Proof.
  unroll.
Qed.

Example unroll_in_unit:
  In 3 [1; 2; 3].
Proof.
  unroll.
Qed.

Example unroll_exists_unit:
  exists e, In (3, e) [(1,1); (2, 2); (3, 3)].
Proof.
  eexists.
  unroll.
Qed.

Example unroll_forall_unit:
  forall e, In e [1; 2; 3] -> In (e, 1) [(1,1); (2, 1); (3, 1)].
Proof.
  intros e He.
  unroll in He; unroll.
Qed.
