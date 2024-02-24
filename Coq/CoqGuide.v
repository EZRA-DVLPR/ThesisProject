(* Sample theorem to learn Coq *)

Definition pierce := forall (p q : Prop),
  ((p -> q) -> p ) -> p. 

Definition lem := forall p, p \/ ~ p.

Theorem pierce_equiv_lem : pierce <-> lem.

(* Proof to show theorem is true *)
Proof.
  unfold pierce, lem.
  firstorder.
  apply H with (q := ~ (p \/ ~ p)).
  firstorder.
  destruct (H p).
  assumption.
  tauto.
Qed.

(* Link here: https://www.youtube.com/watch?v=7sk8hPWAMSw *)


Require Import Coq.Logic.Classical.

Lemma example : forall P Q : Prop, (P \/ Q) /\ ~P -> Q.
Proof.
  intros P Q H.
  destruct H as [H1 H2].
  destruct H1 as [HP | HQ].
  - (* Case 1: P is true *)
    exfalso. apply H2. apply HP.
  - (* Case 2: Q is true *)
    exact HQ.
Qed.

Lemma example_proof : forall P Q : Prop, (P \/ Q) /\ ~P -> Q.
Proof.
  firstorder.
Qed.
