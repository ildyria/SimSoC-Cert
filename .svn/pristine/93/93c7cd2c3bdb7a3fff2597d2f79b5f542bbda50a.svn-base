Require Import Arith.

(* JF: let's consider simple assignments, where the left hand side is just an id *)
(* Otherwise you have to consider side effects when evaluating it, 
  which was not the case in you previous E_Assign
  (you had 
  | E_Assign : forall s t1 s' i t2 n2,
      eval s t1 s (s i) ->
  instead of 
  | E_Assign : forall s t1 s' s'' i t2 n2,
      eval s t1 s' (s i) ->

And introduce definitions for Id 1, etc.

Plus the interesting example.

Next simplification (from opsem1 to opsem2):
replace (option nat, None) by (nat, 0)

Next simplification (from opsem2 to opsem3):
only 2 variables Vx and Vy.

Main advantage: states are just pairs, which are easier to write and read,
and naturally extensional: 
in the usual functional version, 
  update (update Vy 2 st0) Vx 1 
and 
  update (update Vx 1 st0) Vy 2 
are extensionally equal, but not equal.
Here we don't have this issue.
Note however that for big step, [apply E_Assign] becomes less
convenient because it is hard to unify [update i n s] with a pair.
For small-step semantics, no problem.
*)

Inductive id : Type :=  Vx | Vy.

Inductive tm : Type :=
  | C : nat -> tm
  | V : id -> tm
  | P : tm -> tm -> tm
  | A : id -> tm -> tm.

Definition state := (nat * nat)%type.

Definition empty_state : state := (0, 0).

Definition get (st : state) (X: id) : nat :=
  let (vx, vy) := st in
  match X with
  | Vx => vx
  | Vy => vy
  end.

Definition update (st : state) (X: id) (n : nat) : state :=
  let (vx, vy) := st in
  match X with
  | Vx => (n, vy)
  | Vy => (vx, n)
  end.

Eval compute in (update empty_state Vx 2).

Eval compute in get (update empty_state Vx 2) Vx.

(* Deterministic eval, leftmost innermost *)
Inductive eval : state -> tm -> state -> nat -> Prop :=
  | E_Const : forall s n,
      eval s (C n) s n
  | E_Var : forall s i,
      eval s (V i) s (get s i)
  | E_Plus : forall s t1 n1 s' t2 n2 s'',
      eval s t1 s' n1 ->
      eval s' t2 s'' n2 ->
      eval s (P t1 t2) s'' (n1 + n2)
  | E_Assign : forall s i s' t n,
      eval s t s'  n ->
      eval s (A i t) (update s' i n) n.

Definition prog1 := A Vx (C 3).

Example eval1_bs :
  eval empty_state prog1 (update (0, 0) Vx 3) 3.
  apply E_Assign.
  apply E_Const.
Qed.

Definition prog2 := P (A Vx (A Vy (C 1))) (A Vy (C 2)).

Example eval2_bs :
  eval (0, 0) prog2 (1, 2) 3.
  unfold prog2.
  eapply (E_Plus _ _ 1 _ _ 2).
    apply (E_Assign _ Vx (0, 1)). apply (E_Assign _ Vy (0, 0)). apply E_Const.
    apply (E_Assign _ Vy (1, 1)). apply E_Const.
Qed.

(* One small step *)
(* Strategy leftmost innermost *)
Inductive red : tm -> state -> tm -> state -> Prop :=
  | R_Var : forall i st,
      red (V i) st (C (get st i)) st
  | R_PlusConstConst : forall n1 n2 st,
      red (P (C n1) (C n2)) st (C (n1 + n2)) st
  | R_Plus1 : forall t1 st t1' st' t2,
      red t1 st t1' st' ->
      red (P t1 t2) st (P t1' t2) st'
  | R_Plus2 : forall t2 st t2' st' n1,
      red t2 st t2' st' ->
      red (P (C n1) t2) st (P (C n1) t2') st'
  | R_AssignConst : forall i n st,
      red (A i (C n)) st (V i) (update st i n)
      (* updating done but [V i] instead of [C n] : output delayed *)
  | R_AssignRhs : forall i t st t' st',
      red t st t' st' ->
      red (A i t) st (A i t') st'
.

Inductive red_star : tm -> state -> tm -> state -> Prop :=
  | RS_refl : forall t st, red_star t st t st
  | RS_step : forall t1 st1 t2 st2 t3 st3,
    red t1 st1 t2 st2 -> red_star t2 st2 t3 st3 ->
    red_star t1 st1 t3 st3.

Example eval1_ss: 
  red_star prog1 (0, 0) (C 3) (3, 0).
Proof.
unfold prog1.
eapply RS_step. 
  apply R_AssignConst. 
simpl; eapply RS_step. 
  apply R_Var. 
apply RS_refl.
Qed.


Example eval2_ss: 
  red_star prog2 (0, 0) (C 3) (1, 2).
Proof.
unfold prog2.
eapply RS_step.
  apply R_Plus1. apply R_AssignRhs. apply R_AssignConst. 
simpl; eapply RS_step.
  apply R_Plus1. apply R_AssignRhs. apply R_Var. 
simpl; eapply RS_step.
  apply R_Plus1. apply R_AssignConst. 
simpl; eapply RS_step.
  apply R_Plus1. apply R_Var.  
simpl; eapply RS_step.
  apply R_Plus2. apply R_AssignConst.
simpl; eapply RS_step.
  apply R_Plus2. apply R_Var.
simpl; eapply RS_step.
  apply R_PlusConstConst.
apply RS_refl. 
Qed.

