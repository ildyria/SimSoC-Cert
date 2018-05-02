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


New feature (from opsem3 to opsem4): non-determinism.

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

(* Small step semantics *)
(* General definitions for iteration *)

Definition transition := tm -> state -> tm -> state -> Prop.

Inductive star (step: transition) : transition :=
  | ST_refl : forall t st, star step t st t st
  | ST_step : forall t1 st1 t2 st2 t3 st3,
    step t1 st1 t2 st2 -> star step t2 st2 t3 st3 ->
    star step t1 st1 t3 st3.

(* Strategy leftmost innermost *)
Inductive red : transition :=
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

Example eval1_ss: 
  star red prog1 (0, 0) (C 3) (3, 0).
Proof.
unfold prog1.
eapply ST_step. 
  apply R_AssignConst. 
simpl; eapply ST_step. 
  apply R_Var. 
apply ST_refl.
Qed.


Example eval2_ss: 
  star red prog2 (0, 0) (C 3) (1, 2).
Proof.
unfold prog2.
eapply ST_step.
  apply R_Plus1. apply R_AssignRhs. apply R_AssignConst. 
simpl; eapply ST_step.
  apply R_Plus1. apply R_AssignRhs. apply R_Var. 
simpl; eapply ST_step.
  apply R_Plus1. apply R_AssignConst. 
simpl; eapply ST_step.
  apply R_Plus1. apply R_Var.  
simpl; eapply ST_step.
  apply R_Plus2. apply R_AssignConst.
simpl; eapply ST_step.
  apply R_Plus2. apply R_Var.
simpl; eapply ST_step.
  apply R_PlusConstConst.
apply ST_refl. 
Qed.

(* Non deterministic semantics *)

Inductive nd_eval : state -> tm -> state -> nat -> Prop :=
  | NDE_Const : forall s n,
      nd_eval s (C n) s n
  | NDE_Var : forall s i,
      nd_eval s (V i) s (get s i)
  | NDE_Plus_lr : forall s t1 n1 s' t2 n2 s'',
      nd_eval s t1 s' n1 ->
      nd_eval s' t2 s'' n2 ->
      nd_eval s (P t1 t2) s'' (n1 + n2)
  | NDE_Plus_rl : forall s t1 n1 s' t2 n2 s'',
      nd_eval s t2 s' n2 ->
      nd_eval s' t1 s'' n1 ->
      nd_eval s (P t1 t2) s'' (n1 + n2)
  | NDE_Assign : forall s i s' t n,
      nd_eval s t s'  n ->
      nd_eval s (A i t) (update s' i n) n.

Example nd_eval2_bs_lr :
  nd_eval (0, 0) prog2 (1, 2) 3.
  unfold prog2.
  eapply (NDE_Plus_lr _ _ 1 _ _ 2).
    apply (NDE_Assign _ Vx (0, 1)). apply (NDE_Assign _ Vy (0, 0)). apply NDE_Const.
    apply (NDE_Assign _ Vy (1, 1)). apply NDE_Const.
Qed.


(* Same output but different final state *)
Example nd_eval2_bs_rl :
  nd_eval (0, 0) prog2 (1, 1) 3.
  unfold prog2.
  eapply (NDE_Plus_rl _ _ 1 _ _ 2).
    apply (NDE_Assign _ Vy (0, 0)). apply NDE_Const.
    simpl. apply (NDE_Assign _ Vx (0, 1)). apply (NDE_Assign _ Vy (0, 2)). apply NDE_Const.
Qed.



(* No strategy on plus (the left hand side is not constrained to be a value) *)
(* Only R_plus2 is changed *)
Inductive nd_red : transition :=
  | NDR_Var : forall i st,
      nd_red (V i) st (C (get st i)) st
  | NDR_PlusConstConst : forall n1 n2 st,
      nd_red (P (C n1) (C n2)) st (C (n1 + n2)) st
  | NDR_Plus1 : forall t1 st t1' st' t2,
      nd_red t1 st t1' st' ->
      nd_red (P t1 t2) st (P t1' t2) st'
  | NDR_Plus2 : forall t1 st t2 st' t2',
      nd_red t2 st t2' st' ->
      nd_red (P t1 t2) st (P t1 t2') st'
  | NDR_AssignConst : forall i n st,
      nd_red (A i (C n)) st (V i) (update st i n)
      (* updating done but [V i] instead of [C n] : output delayed *)
  | NDR_AssignRhs : forall i t st t' st',
      nd_red t st t' st' ->
      nd_red (A i t) st (A i t') st'
.

Example eval2_ss_lr: 
  star nd_red prog2 (0, 0) (C 3) (1, 2).
Proof.
unfold prog2.
eapply ST_step.
  apply NDR_Plus1. apply NDR_AssignRhs. apply NDR_AssignConst. 
simpl; eapply ST_step.
  apply NDR_Plus1. apply NDR_AssignRhs. apply NDR_Var. 
simpl; eapply ST_step.
  apply NDR_Plus1. apply NDR_AssignConst. 
simpl; eapply ST_step.
  apply NDR_Plus1. apply NDR_Var.  
simpl; eapply ST_step.
  apply NDR_Plus2. apply NDR_AssignConst.
simpl; eapply ST_step.
  apply NDR_Plus2. apply NDR_Var.
simpl; eapply ST_step.
  apply NDR_PlusConstConst.
apply ST_refl. 
Qed.


Example eval2_ss_rl: 
  star nd_red prog2 (0, 0) (C 3) (1, 1).
Proof.
unfold prog2.
eapply ST_step.
  apply NDR_Plus2. apply NDR_AssignConst. 
simpl; eapply ST_step.
  apply NDR_Plus2. apply NDR_Var.
simpl; eapply ST_step.
  apply NDR_Plus1. apply NDR_AssignRhs. apply NDR_AssignConst. 
simpl; eapply ST_step.
  apply NDR_Plus1. apply NDR_AssignRhs. apply NDR_Var. 
simpl; eapply ST_step.
  apply NDR_Plus1. apply NDR_AssignConst.
simpl; eapply ST_step.
  apply NDR_Plus1. apply NDR_Var.
simpl; eapply ST_step.
  apply NDR_PlusConstConst.
apply ST_refl. 
Qed.

Example eval2_ss_mix: 
  star nd_red prog2 (0, 0) (C 4) (2, 2).
Proof.
unfold prog2.
eapply ST_step.
  apply NDR_Plus1. apply NDR_AssignRhs. apply NDR_AssignConst. 
simpl; eapply ST_step.
  apply NDR_Plus2. apply NDR_AssignConst.
simpl; eapply ST_step.
  apply NDR_Plus2. apply NDR_Var.
simpl; eapply ST_step.
  apply NDR_Plus1. apply NDR_AssignRhs. apply NDR_Var. 
simpl; eapply ST_step.
  apply NDR_Plus1. apply NDR_AssignConst. 
simpl; eapply ST_step.
  apply NDR_Plus1. apply NDR_Var.  
simpl; eapply ST_step.
  apply NDR_PlusConstConst.
apply ST_refl. 
Qed.




