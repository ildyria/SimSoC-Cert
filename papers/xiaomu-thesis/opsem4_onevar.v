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

Additional simplification: only 1 variable
(should be enough to show interesting examples,
e.g. x + (x=1) + (x=2) or (x=x+1) + (x=2)
*)


Inductive tm : Type :=
  | C : nat -> tm      (* constant *)
  | V : tm             (* the unique variable *)
  | P : tm -> tm -> tm (* plus *)
  | A : tm -> tm       (* assignment *)
.

Definition state := nat.

Definition empty_state : state := 0.

(* Deterministic eval, leftmost innermost *)


(* original definition *)
Inductive eval : state -> tm -> state -> nat -> Prop :=
  | E_Const : forall s n,
      eval s (C n) s n
  | E_Var : forall s,
      eval s V s s
  | E_Plus : forall s t1 n1 s' t2 n2 s'',
      eval s t1 s' n1 ->
      eval s' t2 s'' n2 ->
      eval s (P t1 t2) s'' (n1 + n2)
  | E_Assign : forall s s' s'' t n1 n2,
      eval s t s' n1 ->
      eval n1 V s'' n2 ->
      eval s (A t) s'' n2
.

(*
(* Not accepted because the type of ea does not provide enough information *)
Inductive eval_gen (ea: eval_type -> Prop) : eval_type :=
  | E_Const : forall s n,
      eval_gen ea s (C n) s n
  | E_Var : forall s,
      eval_gen ea s V s s
  | E_Plus : forall s t1 n1 s' t2 n2 s'',
      eval_gen ea s t1 s' n1 ->
      eval_gen ea s' t2 s'' n2 ->
      eval_gen ea s (P t1 t2) s'' (n1 + n2)
  | E_Assign : ea (eval_gen ea)
.
*)

Inductive kind_assign : Set := KA_simple | KA_decomposed.

Definition is_simple ka := 
  match ka with
    | KA_simple => True
    | KA_decomposed => False
  end.

Definition is_decomposed ka := 
  match ka with
    | KA_simple => False
    | KA_decomposed => True
  end.

Definition eval_type := state -> tm -> state -> nat -> Prop.

Definition simpler_eval (eval: eval_type) :=
      forall s s' t n,
      eval s t s' n ->
      eval s (A t) n n.

Definition decomposed_eval (eval: eval_type) :=
      forall s s' s'' t n1 n2,
      eval s t s' n1 ->
      eval n1 V s'' n2 ->
      eval s (A t) s'' n2.

Inductive eval_gen (ka : kind_assign) : eval_type :=
  | EG_Const : forall s n,
      eval_gen ka s (C n) s n
  | EG_Var : forall s,
      eval_gen ka s V s s
  | EG_Plus : forall s t1 n1 s' t2 n2 s'',
      eval_gen ka s t1 s' n1 ->
      eval_gen ka s' t2 s'' n2 ->
      eval_gen ka s (P t1 t2) s'' (n1 + n2)
  | EG_Assign : is_decomposed ka -> decomposed_eval (eval_gen ka)
  | EG_Assign_simpl : is_simple ka -> simpler_eval (eval_gen ka)
.

Definition eval_decomposed := eval_gen KA_decomposed.
Definition eval_simpl := eval_gen KA_simple.

(* eval_decomposed is really eval *)

Lemma eval_eval_decomposed :
 forall s s' t n, eval s s' t n -> eval_decomposed s s' t n.
Proof.
intros s s' t n e; elim e; clear e s s' t n.
  constructor.
  constructor.
  intros s t1 n1 s' t2 n2 s'' _ IH1 _ IH2; apply EG_Plus with s'; assumption.
  intros s s' s'' t n1 n2 _ e1 _ e2;
    exact (EG_Assign KA_decomposed I _ _ _ _ _ _ e1 e2). 
Qed.

Lemma decomposed_simpl : 
  forall s s' t n, eval_decomposed s s' t n -> eval s s' t n.
Proof.
intros s s' t n e; elim e; clear e s s' t n.
  constructor.
  constructor.
  intros s t1 n1 s' t2 n2 s'' _ IH1 _ IH2; apply E_Plus with s'; assumption.
  intros _ s s' s'' t n1 n2 _ e1 _ e2. eapply E_Assign; eassumption.
  intro F; case F.
Qed.

(* Equivalence *)

Lemma E_Assign_simpl_derived : simpler_eval eval_decomposed.
Proof.
intros s s' t n e. eapply EG_Assign. 
  exact I.
  apply e.
  apply EG_Var.
Qed.

Lemma E_Assign_derived : decomposed_eval eval_simpl.
Proof.
intros s s' s'' t n1 n2 e1 e2. 
inversion e2; subst.
apply (EG_Assign_simpl KA_simple I _ _ _ _ e1).
Qed.

Lemma simpl_decomposed : forall s s' t n, eval_simpl s s' t n -> eval_decomposed s s' t n.
Proof.
intros s s' t n e; elim e; clear e s s' t n.
  constructor.
  constructor.
  intros s t1 n1 s' t2 n2 s'' _ IH1 _ IH2; apply EG_Plus with s'; assumption.
  intro F; case F.
  intros _ s s' t n _; apply E_Assign_simpl_derived.
Qed.

Lemma decomposed_simpl : forall s s' t n, eval_decomposed s s' t n -> eval_simpl s s' t n.
Proof.
intros s s' t n e; elim e; clear e s s' t n.
  constructor.
  constructor.
  intros s t1 n1 s' t2 n2 s'' _ IH1 _ IH2; apply EG_Plus with s'; assumption.
  intros _ s s' s'' t n1 n2 _ e1 _ e2. eapply E_Assign_derived; eassumption.
  intro F; case F.
Qed.

(*
Lemma assign_eq :
  forall s s' t n2,
  eval s (A t) s' n2 -> eval s (A t) n2 n2.
Proof.
  intros.
  inversion H. subst.
  apply E_Assign with s'0 n1.
  apply H1.
  inversion H3.
  apply E_Var.
Qed.

Lemma assign_eq' :
  forall s s' s'' t n1 n2,
  eval s t s' n1 -> eval n1 V s'' n2 -> eval s (A t) n2 n2.
Proof.
  intros. 
  apply E_Assign with s' n1.
  apply H.
  inversion H0. subst.
  apply H0.
Qed.

Lemma simpl_assign_eq' :
  forall s s' t n,
  eval s (A t) n n -> eval n V s' n -> eval s (A t) s' n.
Proof.
  intros. 
  inversion H. subst.
  apply E_Assign with s'0 n1.
  apply H2.
  inversion H4. subst.
  apply H0.
Qed.

*)
  
Lemma eval_deterministic:
  forall st t st' st'' v v',
  eval st t st' v ->
  eval st t st'' v' ->
  (v = v') /\ (st' = st'').
Proof.
  intros until v'; intros ev1 ev2.
  generalize dependent v'.
  generalize dependent st''.
  induction ev1.
  (*Case "C"*)
  intros;
  inversion ev2; subst; split; try reflexivity.
  (*Case "V"*)
  intros;
  inversion ev2; subst; split; try reflexivity.
  (*Case "P"*)
  intros;
  inversion ev2; subst; split;
  apply IHev1_1 in H2; destruct H2 as [Heqn1 Heqst1];
  rewrite Heqst1 in IHev1_2;
  apply IHev1_2 in H5; destruct H5 as [Heqn2 Heqst2];
  [rewrite Heqn1; rewrite Heqn2; reflexivity|exact Heqst2].
  (*Case "A"*)
  intros;
  inversion ev2; subst.
  destruct (IHev1_1 _ _ H0).
  apply IHev1_2. rewrite H. assumption.
Qed.


Definition prog1 := A (C 3).

Example eval1_bs :
  eval empty_state prog1 3 3.
  eapply E_Assign.
    apply E_Const.
    apply E_Var.
Qed.

Definition prog2 := P V (P (A (C 1)) (A (C 2))).

Example eval2_bs :
  eval 0 prog2 2 3.
  unfold prog2.
  apply (E_Plus _ _ 0 0 _ 3).
    eapply E_Var. 
    apply (E_Plus _ _ 1 1 _ 2).
      eapply E_Assign; [apply E_Const | apply E_Var].
      eapply E_Assign; [apply E_Const | apply E_Var].
Qed.

(* Small step semantics *)
(* General definitions for iteration *)

Definition transition := tm -> state -> tm -> state -> Prop.

Inductive star (step: transition) : transition :=
  | ST_refl : forall t st, star step t st t st
  | ST_step : forall t1 st1 t2 st2 t3 st3,
    step t1 st1 t2 st2 -> star step t2 st2 t3 st3 ->
    star step t1 st1 t3 st3.

(* One small step *)
(* Strategy leftmost innermost *)
Inductive red : transition := 
  | R_Var : forall st,
      red V st (C st) st
  | R_PlusConstConst : forall n1 n2 st,
      red (P (C n1) (C n2)) st (C (n1 + n2)) st
  | R_Plus1 : forall t1 st t1' st' t2,
      red t1 st t1' st' ->
      red (P t1 t2) st (P t1' t2) st'
  | R_Plus2 : forall t2 st t2' st' n1,
      red t2 st t2' st' ->
      red (P (C n1) t2) st (P (C n1) t2') st'
  | R_AssignConst : forall n st,
      red (A (C n)) st V n
      (* updating done but reduce to [V] instead of [C n] : output delayed *)
  | R_AssignRhs : forall t st t' st',
      red t st t' st' ->
      red (A t) st (A t') st'
.


Example eval1_ss:   star red prog1 0 (C 3) 3.
Proof.
unfold prog1.
eapply ST_step. apply R_AssignConst. 
eapply ST_step. apply R_Var. 
apply ST_refl.
Qed.


Example eval2_ss:   star red prog2 0 (C 3) 2.
Proof.
unfold prog2.
eapply ST_step. apply R_Plus1. apply R_Var.
eapply ST_step. apply R_Plus2. apply R_Plus1. apply R_AssignConst. 
eapply ST_step. apply R_Plus2. apply R_Plus1. apply R_Var. 
eapply ST_step. apply R_Plus2. apply R_Plus2. apply R_AssignConst. 
eapply ST_step. apply R_Plus2. apply R_Plus2. apply R_Var. 
eapply ST_step. apply R_Plus2. apply R_PlusConstConst. 
eapply ST_step. apply R_PlusConstConst. 
apply ST_refl. 
Qed.

(* Non deterministic semantics *)

Inductive nd_eval : state -> tm -> state -> nat -> Prop :=
  | NDE_Const : forall s n,
      nd_eval s (C n) s n
  | NDE_Var : forall s,
      nd_eval s V s s
  | NDE_Plus_lr : forall s t1 n1 s' t2 n2 s'',
      nd_eval s t1 s' n1 ->
      nd_eval s' t2 s'' n2 ->
      nd_eval s (P t1 t2) s'' (n1 + n2)
  | NDE_Plus_rl : forall s t1 n1 s' t2 n2 s'',
      nd_eval s t2 s' n2 ->
      nd_eval s' t1 s'' n1 ->
      nd_eval s (P t1 t2) s'' (n1 + n2)
  | NDE_Assign : forall s s' s'' t n1 n2,
      nd_eval s t s' n1 ->
      nd_eval n1 V s'' n2 ->
      nd_eval s (A t) s'' n2
.

Lemma simpl_NDE_assign : 
  forall s s' t n, nd_eval s t s' n ->  nd_eval s (A t) n n.
Proof.
intros s s' t n e. eapply NDE_Assign. 
  apply e.
  apply NDE_Var.
Qed.


(* different output and different final state *)
Example nd_eval2_bs_lr :
  nd_eval 0 prog2 1 4.
  unfold prog2.
  apply (NDE_Plus_rl _ _ 1 1 _ 3).
    apply (NDE_Plus_rl _ _ 1 2 _ 2).
      eapply NDE_Assign; [apply NDE_Const | apply NDE_Var].
      eapply NDE_Assign; [apply NDE_Const | apply NDE_Var].
    eapply NDE_Var. 
Qed.

(* Other are possible for nd_eval prog2 *)



(* No strategy on plus (the left hand side is not constrained to be a value) *)
(* Only R_plus2 is changed *)

Inductive nd_red : transition := 
  | NDR_Var : forall st,
      nd_red V st (C st) st
  | NDR_PlusConstConst : forall n1 n2 st,
      nd_red (P (C n1) (C n2)) st (C (n1 + n2)) st
  | NDR_Plus1 : forall t1 st t1' st' t2,
      nd_red t1 st t1' st' ->
      nd_red (P t1 t2) st (P t1' t2) st'
  | NDR_Plus2 : forall t1 st t2 st' t2',
      nd_red t2 st t2' st' ->
      nd_red (P t1 t2) st (P t1 t2') st'
  | NDR_AssignConst : forall n st,
      nd_red (A (C n)) st V n
      (* updating done but reduce to [V] instead of [C n] : output delayed *)
  | NDR_AssignRhs : forall t st t' st',
      nd_red t st t' st' ->
      nd_red (A t) st (A t') st'
.

Example eval2_ss_rr_rl:   star nd_red prog2 0 (C 3) 1.
Proof.
unfold prog2.
eapply ST_step. apply NDR_Plus2. apply NDR_Plus2. apply NDR_AssignConst.
eapply ST_step. apply NDR_Plus2. apply NDR_Plus1. apply NDR_AssignConst. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus1. apply NDR_Var.
eapply ST_step. apply NDR_Plus2. apply NDR_Plus2. apply NDR_Var. 
eapply ST_step. apply NDR_Plus1. apply NDR_Var. 
eapply ST_step. apply NDR_Plus2. apply NDR_PlusConstConst.
eapply ST_step. apply NDR_PlusConstConst. 
apply ST_refl. 
Qed.

Example eval2_ss_lr_lr:   star nd_red prog2 0 (C 3) 2.
Proof.
unfold prog2.
eapply ST_step. apply NDR_Plus1. apply NDR_Var.
eapply ST_step. apply NDR_Plus2. apply NDR_Plus1. apply NDR_AssignConst. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus1. apply NDR_Var. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus2. apply NDR_AssignConst. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus2. apply NDR_Var. 
eapply ST_step. apply NDR_Plus2. apply NDR_PlusConstConst. 
eapply ST_step. apply NDR_PlusConstConst. 
apply ST_refl. 
Qed.

Example eval2_ss_rl_rl:   star nd_red prog2 0 (C 4) 1.
Proof.
unfold prog2.
eapply ST_step. apply NDR_Plus2. apply NDR_Plus2. apply NDR_AssignConst. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus2. apply NDR_Var. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus1. apply NDR_AssignConst. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus1. apply NDR_Var. 
eapply ST_step. apply NDR_Plus2. apply NDR_PlusConstConst. 
eapply ST_step. apply NDR_Plus1. apply NDR_Var.
eapply ST_step. apply NDR_PlusConstConst. 
apply ST_refl. 
Qed.

Example eval2_ss_rl_lr:   star nd_red prog2 0 (C 5) 2.
Proof.
unfold prog2.
eapply ST_step. apply NDR_Plus2. apply NDR_Plus1. apply NDR_AssignConst. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus1. apply NDR_Var. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus2. apply NDR_AssignConst. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus2. apply NDR_Var. 
eapply ST_step. apply NDR_Plus2. apply NDR_PlusConstConst. 
eapply ST_step. apply NDR_Plus1. apply NDR_Var.
eapply ST_step. apply NDR_PlusConstConst. 
apply ST_refl. 
Qed.

(* Impossible to obtain with ND big step semantics *)
Example eval2_ss_race:   star nd_red prog2 0 (C 6) 2.
Proof.
unfold prog2.
eapply ST_step. apply NDR_Plus2. apply NDR_Plus1. apply NDR_AssignConst. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus2. apply NDR_AssignConst.
(* (* No assignment from now, all strategies converge *)
eapply ST_step. apply NDR_Plus1. apply NDR_Var.
eapply ST_step. apply NDR_Plus2. apply NDR_Plus1. apply NDR_Var. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus2. apply NDR_Var.
eapply ST_step. apply NDR_Plus2. apply NDR_PlusConstConst.
eapply ST_step. apply NDR_PlusConstConst. 
apply ST_refl.  
Qed.
*) 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus1. apply NDR_Var. 
eapply ST_step. apply NDR_Plus2. apply NDR_Plus2. apply NDR_Var. 
eapply ST_step. apply NDR_Plus2. apply NDR_PlusConstConst. 
eapply ST_step. apply NDR_Plus1. apply NDR_Var.
eapply ST_step. apply NDR_PlusConstConst. 
apply ST_refl. 
Qed.
