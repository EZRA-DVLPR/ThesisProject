Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments

Inductive binop : Set := Plus | Times

Inductive exp : Set := 
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp

(* 
Definitions that are not as concise

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

Definition binopDenote : binop -> nat -> nat -> nat :=
  fun (b : binop) =>
    match b with
      | Plus => plus
      |Times => mult
    end.
 *)

Definition binopDenote := fun b =>
  match b with
    |Plus => plus
    |Times => mult
  end

Fixpoint expDenote (e : exp) : nat :=
  match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end

Eval simpl in expDenote (Const 42)
  = 42 : nat




Coq < Check 0.