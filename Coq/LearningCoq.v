(* Chapter 2 Notes *)

Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments

(* 2.1.1 *)

Inductive binop : Set := Plus | Times

Inductive exp : Set := 
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp

(* 
Definitions that are not as concise as the following one.T

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

Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).
  = 4 : nat

Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).
  = 28 : nat

(* Compile into a target language(s) = Stack machine *)
(* 2.1.2 *)

Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr

Definition prog := list instr
Definition stack := list nat

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
    |iConst n => Some (n :: s)
    |iBinop b =>
      match s with
        |arg1 :: arg2 :: s' =>
          some ((binopDenote b) arg1 arg2 :: s')
        |_ => None
      end
  end
  

Fixpoint progDenote (p : prog) (s : stack) : ooption stack :=
  match p with
    | nil => Some s
    | i :: p' =>
      match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
      end
  end


(* Translation (writing the compiler) *)
(* 2.1.3 *)

Fixpoint compile (e : exp) : prog :=
  match e with
    | Const n => iConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compil e1 ++ iBinop b :: nil
  end

(* Test runs for compiler *)

Eval simpl in compile (Const 42)
  = iConst 42 :: nil : prog

Eval simpl in compile (Binop Plus (Const 2) (Const 2))
  = iConst 2 :: iConst 2 :: iBinop Plus :: nil : prog

Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))
  = iConst 7 :: iConst 2 :: iConst 2 :: iBinop Plus : iBinop Times :: nil : prog

(* Run compiled programs written beforehead *)

Eval simpl in progDenote (compile (Const 42)) nil
  = Some (42 :: nil) : option stack

Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil
  = Some (4 :: nil) : option stack

Eval simpl in progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))) nil
  = Some (28 :: nil) : option stack

(* Correctness proof for compiler *)
(* 2.1.4 *)

Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e ::nil)

Abort.
Lemma compile_correct' : forall e p s, progDenote (compile e++ p) s = progDenote p (expDenote e ::s)

(* Best to prove the subgoals in the order coq finds them *)
induction e

intros.

unfold compile.

unfold expDenote.

unfold progDenote at 1.

simpl.

fold progDenote

reflexivity.

intros.
unfold compile.
fold compile.
unfold expDenote.
fold expDenote.

Check app_assoc_reverse
(* this is what the above function does *)
app_assoc : forall (A : Type) (l m n : list A), (l ++m) ++ n = l ++ m ++ n

rewrite IHe2.

rewrite app_assoc_reverse.
rewrite IHe1.

unfold progDenote at 1.
simpl.
fold progDenote.
reflexivity.
(* Proof completed *)
Qed.

(* concise version of proof above *)
Lemma compile_correct' : forall e s p, progDenote (compile e ++0) s = progDenote p (expDenote e ::s).
induction e; crush.
Qed.


(* Now we can prove the main theorem easily. *)

Theorem compile_corrrect : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
intros.
Check app_nil_end.
rewrite(app_nil_end (compile e)).
rewrit compile_correct'.

reflexivity
Qed.



(* Typed Expressions *)
(* 2.2 *)

(* define a trivial language to classify expressions *)
(* 2.2.1 *)

Inductive type : Set := Nat | Bool.

(* expanded set of binary  ops *)

Inductive tbinopg : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLe : tbinop Nat Nat Bool.

(* 
type has been defined as an indexed type family.

tbinop t1 t2 t

can be looked at as a binary operator with operands of type t1 and t2.
with a result in type t.

 *)

(* set of typed expressions *)

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp 2.

(* Path to creating an interpreter *)

Definition typeDenote (t : type) : Set :=
  match t with
    |Nat => nat
    |Bool => bool
  end.

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res) : typeDenote arg1 -> typeDenote arg2 -> typeDenote res := 
  match b with
    | TPlus => plus
    | TTimes => mult
    |TEq Nat => beq_nat
    |TEq Bool => eqb
    | TLe => leb
  end.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e
    | TNConst n => n
    | TBConst b => b
    | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

(* evaluation of semantics *)

Eval simpl in texpDenote (TNConst 42).
  = 42 : typeDenote Nat

Eval simpl in texpDenote (TBConst true).
  = true : typeDenote Bool

Eval simpl in texp 


(* ... CoqIDE crashed on me. *)

(* see the book chapter 2 for the rest. *)






















