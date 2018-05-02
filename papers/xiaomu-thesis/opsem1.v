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

*)

Inductive id : Type :=
  Id : nat -> id.

Definition Vx := Id 1.
Definition Vy := Id 2.

Inductive tm : Type :=
  | C : nat -> tm
  | V : id -> tm
  | P : tm -> tm -> tm
  | A : id -> tm -> tm.

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Definition state := id -> option nat.

Definition empty_state : state :=
  fun _ => None.

Definition update_xm (st : state) (X: id) (n : option nat) : state :=
  fun X' => if beq_id X X' then n else st X'.

(* JF: update just takes a nat as a snd argument *)
Definition update (st : state) (X: id) (n : nat) : state :=
  fun X' => if beq_id X X' then Some n else st X'.

Eval compute in (update empty_state Vx 2) Vx.

(* Deterministic eval, leftmost innermost *)
Inductive eval : state -> tm -> state -> option nat -> Prop :=
  | E_Const : forall s n,
      eval s (C n) s (Some n)
  | E_Var : forall s i,
      eval s (V i) s (s i)
  | E_Plus : forall s t1 n1 s' t2 n2 s'',
      eval s t1 s' (Some n1) ->
      eval s' t2 s'' (Some n2) ->
      eval s (P t1 t2) s'' (Some (n1 + n2))
  | E_Assign : forall s i s' t n,
      eval s t s' (Some n) ->
      eval s (A i t) (update s' i n) (Some n).

Definition prog1 := A Vx (C 3).

Example eval1_bs :
  eval empty_state prog1 (update empty_state Vx 3) (Some 3).
  apply E_Assign.
  apply E_Const.
Qed.

Definition prog2 := P (A Vx (A Vy (C 1))) (A Vy (C 2)).
Definition st1 := update empty_state Vy 1.
Definition st2 := update st1 Vx 1.
Definition st3 := update st2 Vy 2.

Example eval2_bs :
  eval empty_state prog2 st3 (Some 3).
  unfold prog2.
  apply (E_Plus _ _ 1 st2 _ 2).
    apply E_Assign. apply E_Assign. apply E_Const.
  apply E_Assign. apply E_Const.
Qed.

(* One small step *)
(* Strategy leftmost innermost *)
Inductive red : tm -> state -> tm -> state -> Prop :=
  | R_Var : forall i st n, 
      st i = Some n ->
      red (V i) st (C n) st
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
  red_star prog1 empty_state (C 3) (update empty_state Vx 3).
unfold prog1.
eapply RS_step. 
  apply R_AssignConst. 
simpl; eapply RS_step. 
  apply R_Var. unfold update; simpl; reflexivity.
  apply RS_refl.
Qed.


Example eval2_ss: 
  red_star prog2 empty_state (C 3) st3.
Proof.
unfold prog2.
eapply RS_step.
  apply R_Plus1. apply R_AssignRhs. apply R_AssignConst. 
simpl; eapply RS_step.
  apply R_Plus1. apply R_AssignRhs. apply R_Var. unfold update; simpl; reflexivity.
simpl; eapply RS_step.
  apply R_Plus1. apply R_AssignConst. 
simpl; eapply RS_step.
  apply R_Plus1. apply R_Var. unfold update; simpl; reflexivity.
simpl; eapply RS_step.
  apply R_Plus2. apply R_AssignConst.
simpl; eapply RS_step.
  apply R_Plus2. apply R_Var. unfold update; simpl; reflexivity.
simpl; eapply RS_step.
  apply R_PlusConstConst.
apply RS_refl. 
Qed.
