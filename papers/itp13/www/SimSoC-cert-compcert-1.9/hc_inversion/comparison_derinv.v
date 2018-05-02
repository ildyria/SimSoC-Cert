Require Import Globalenvs Memory.
Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors. 
Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import adc_compcert.
Require Import projection.
Require Import hcinv_eval_expr.

Require Import Arm6_Simul.
Import Arm6_Functions.Semantics.

Definition prog_adc := p.

Lemma functions_behavior_ok:
  forall e l b s vf fd m vargs t m' vres l' b' s',
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    Genv.find_funct (Genv.globalenv prog_adc) vf = Some fd ->
    eval_funcall (Genv.globalenv prog_adc) m fd vargs t m' vres ->
    proc_state_related m' e (Ok tt (mk_semstate l' b' s')).
Proof.
Admitted.

(* AST for: copy_StatusRegister(&proc->cpsr, spsr(proc)) *)
(* See more details in ../../pieces_of_simlight_code.c   *)
Definition cp_SR :=
  Ecall
  (Evalof (Evar copy_StatusRegister T14) T14)
  (Econs
    (Eaddrof
      (Efield
        (Ederef (Evalof (Evar adc_compcert.proc T3) T3) T6)
        cpsr T7) T8)
    (Econs
      (Ecall (Evalof (Evar spsr T15) T15)
        (Econs (Evalof (Evar adc_compcert.proc T3) T3)
          Enil) T8) Enil)) T12.

Derive Inversion leminveval with (forall ge e m k a t m' a', eval_expr ge e m k a t m' a')
  Sort Prop.

Derive Inversion leminveval_list with (forall ge e m a t m' a', eval_exprlist ge e m a t m' a')
  Sort Prop.

Lemma same_cp_SR' :
  forall e m l b s t m' v em,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    eval_expression (Genv.globalenv prog_adc) e m cp_SR t m' v ->
    proc_state_related m' e
      (Ok tt (mk_semstate l b
      (Arm6_State.set_cpsr s (Arm6_State.spsr s em)))).
Proof.
  intros until em. intros psrel cpsr.
  inv cpsr.
  unfold cp_SR in H.
  Time (
  inversion H using leminveval; try discriminate;
  intros; subst; clear H;
  injection H11; intros; subst; clear H11 H1 H10;
  inversion H2 using leminveval; try discriminate;
  intros; subst; clear H2;
  injection H10; intros; subst; clear H10 H H9;
  inversion H14 using leminveval; try discriminate;
  intros; subst; clear H14;
  injection H9; intros; subst; clear H H9 H8;
  inversion H3 using leminveval_list; try discriminate;
  intros; subst; clear H3;
  injection H8; intros; subst; clear H H8;
  inversion H12 using leminveval; try discriminate;
  intros; subst; clear H12;
  injection H8; intros; subst; clear H H8 H3;
  inversion H14 using leminveval; try discriminate;
  intros; subst; clear H14;
  injection H8; intros; subst; clear H H8 H3;
  inversion H12 using leminveval; try discriminate;
  intros; subst; clear H12;
  injection H8; intros; subst; clear H H8 H3;
  inversion H14 using leminveval; try discriminate;
  intros; subst; clear H14;
  injection H8; intros; subst; clear H H8 H3;
  inversion H12 using leminveval; try discriminate;
  intros; subst; clear H12;
  injection H8; intros; subst; clear H H8 H3;
  inversion H13 using leminveval_list; try discriminate;
  intros; subst; clear H13;
  injection H1; intros; subst; clear H1 H;
  inversion H11 using leminveval; try discriminate;
  intros; subst; clear H11;
  injection H1; intros; subst; clear H1 H H10;
  inversion H3 using leminveval; try discriminate;
  intros; subst; clear H3;
  injection H9; intros; subst; clear H H8 H9;
  inversion H14 using leminveval; try discriminate;
  intros; subst; clear H14;
  injection H8; intros; subst; clear H H8 H3;
  inversion H17 using leminveval_list; try discriminate;
  intros; subst; clear H17;
  injection H1; intros; subst; clear H1 H;
  inversion H11 using leminveval; try discriminate;
  intros; subst; clear H11;
  injection H8; intros; subst; clear H H8 H3;
  inversion H17 using leminveval; try discriminate;
  intros; subst; clear H17;
  injection H8; intros; subst; clear H H8 H3;
  inversion H13 using leminveval_list; try discriminate;
  intros; subst; clear H13; clear H3 H;
  inversion H12 using leminveval_list; try discriminate;
  intros; subst; clear H12; clear H3 H).
  (* Function spsr, get spsr from the current state *)
  apply (functions_behavior_ok e l b s vf0 fd0 m5 vargs0 t5 m2 vres0 l b s)
    in psrel; [idtac|exact H21|exact H23].
  (* Function copy_StatusRegister, copy the current spsr to cpsr*)
  apply (functions_behavior_ok e l b s vf fd m2 vargs t3 m' vres l b
    (Arm6_State.set_cpsr s (Arm6_State.spsr s em))) in psrel;
  [idtac|exact H7|exact H16].
  exact psrel.
Qed.
  
