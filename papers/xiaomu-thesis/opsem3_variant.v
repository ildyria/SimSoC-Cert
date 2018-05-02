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

Variant (from opsem3 to opsem3_variant):
variables are inlined in tm.
Advantage: no need for update and get.
Drawback: duplication of rules.
*)


Inductive tm : Type :=
  | C : nat -> tm
  | Vx : tm
  | Vy : tm
  | P : tm -> tm -> tm
  | Ax : tm -> tm
  | Ay : tm -> tm.

Definition state := (nat * nat)%type.

Definition empty_state : state := (0, 0).

(* JF: update just takes a nat as a snd argument *)
(*
Definition update (st : state) (X: id) (n : nat) : state :=
  let (vx, vy) := st in
  match X with
  | Vx => (n, vy)
  | Vy => (vx, n)
  end.

Eval compute in (update empty_state Vx 2).
*)

(* Deterministic eval, leftmost innermost *)
Inductive eval : state -> tm -> state -> nat -> Prop :=
  | E_Const : forall s n,
      eval s (C n) s n
  | E_Varx : forall vx vy,
      eval (vx, vy) Vx (vx, vy) vx
  | E_Vary : forall vx vy,
      eval (vx, vy) Vy (vx, vy) vy
  | E_Plus : forall s t1 n1 s' t2 n2 s'',
      eval s t1 s' n1 ->
      eval s' t2 s'' n2 ->
      eval s (P t1 t2) s'' (n1 + n2)
  | E_Assignx : forall s vx' vy' t n,
      eval s t (vx', vy') n ->
      eval s (Ax t) (n, vy') n
  | E_Assigny : forall s vx' vy' t n,
      eval s t (vx', vy') n ->
      eval s (Ay t) (vx', n) n.

Definition prog1 := Ax (C 3).

Example eval1_bs :
  eval empty_state prog1 (3, 0) 3.
  eapply E_Assignx.
  apply E_Const.
Qed.

Definition prog2 := P (Ax (Ay (C 1))) (Ay (C 2)).

Example eval2_bs :
  eval empty_state prog2 (1, 2) 3.
  unfold prog2.
  apply (E_Plus _ _ 1 (1, 1) _ 2).
    eapply E_Assignx. eapply E_Assigny. apply E_Const.
    eapply E_Assigny. apply E_Const.
Qed.

(* One small step *)
(* Strategy leftmost innermost *)
Inductive red : tm -> state -> tm -> state -> Prop :=
  | R_PlusConstConst : forall n1 n2 st,
      red (P (C n1) (C n2)) st (C (n1 + n2)) st
  | R_Plus1 : forall t1 st t1' st' t2,
      red t1 st t1' st' ->
      red (P t1 t2) st (P t1' t2) st'
  | R_Plus2 : forall t2 st t2' st' n1,
      red t2 st t2' st' ->
      red (P (C n1) t2) st (P (C n1) t2') st'
  | R_AssignConstx : forall n vx vy,
      red (Ax (C n)) (vx, vy) (C n) (n, vy)
  | R_AssignConsty : forall n vx vy,
      red (Ay (C n)) (vx, vy) (C n) (vx, n)
  | R_AssignRhsx : forall t st t' st',
      red t st t' st' ->
      red (Ax t) st (Ax t') st'
  | R_AssignRhsy : forall t st t' st',
      red t st t' st' ->
      red (Ay t) st (Ay t') st'
.

Inductive red_star : tm -> state -> tm -> state -> Prop :=
  | RS_refl : forall t st, red_star t st t st
  | RS_step : forall t1 st1 t2 st2 t3 st3,
    red t1 st1 t2 st2 -> red_star t2 st2 t3 st3 ->
    red_star t1 st1 t3 st3.


Example eval1_ss: 
  red_star prog1 empty_state (C 3) (3, 0).
Proof.
unfold prog1.
eapply RS_step. 
  apply R_AssignConstx. 
  apply RS_refl.
Qed.


Example eval2_ss: 
  red_star prog2 empty_state (C 3) (1, 2).
Proof.
unfold prog2.
eapply RS_step.
  apply R_Plus1. apply R_AssignRhsx. apply R_AssignConsty. 
  eapply RS_step.
    apply R_Plus1. apply R_AssignConstx. 
    eapply RS_step.
      apply R_Plus2. apply R_AssignConsty.
      eapply RS_step.
        apply R_PlusConstConst.
        apply RS_refl. 
Qed.
