Inductive unit : Set :=
  | tt.

Check unit.

Check tt.

Theorem unit_singleton : forall x : unit, x = tt.

Proof.

induction x.

reflexivity.

Qed.

Check unit_ind.

Inductive Empty_set : Set := .

(* Empty set is the Curry-Howard equivalent of False. *)

(* Defining the booleans *)

Inductive bool : Set :=
| true
| false.

(* pattern matching defn *)
Definition negb (b : bool) : bool :=
  match b with
    |true => false
    |false => true
  end.

(* Alt. defn *)
Definition negb' (b : bool) : bool :=
  if b then false else true.

(* proof that negb is its own inverse op *)

Theorem negb_inverse : forall b : bool, negb (negb b) = b.

Proof.
destruct b.
reflexivity.
Restart.
destruct b; reflexivity.
Qed.

(* thm about booleans show another tactic *)

Theorem negb_ineq : forall b : bool, negb b <> b.

Proof.
destruct b; discriminate.
Qed.

(* 
discriminate is used to prove that 2 values of an inductive type
are not equal if the values are formed with diff constructors 
*)

