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
  (Ecall
    (Evalof (Evar copy_StatusRegister T32) T32)
    (Econs
      (Eaddrof
        (Efield
          (Evalof
            (Ederef 
              (Evalof (Evar proc T2) T2) T8)
            T8) cpsr T9) T25)
      (Econs
        (Ecall (Evalof (Evar spsr T33) T33)
          (Econs (Evalof (Evar proc T2) T2)
            Enil) T25) Enil)) T10).

(* ------------------------------------------------------------ *)
(* Use hc_inversion to invert type eval_expr *)

Lemma same_cp_SR_hcinv :
  forall e m l b s t m' v em,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    eval_expression (Genv.globalenv prog_adc) e m cp_SR t m' v ->
    proc_state_related m' e
      (Ok tt (mk_semstate l b
      (Arm6_State.set_cpsr s (Arm6_State.spsr s em)))).
Proof.
  intros until em. intros psrel cpsr.
  inversion cpsr. subst. rename H into ee,H0 into esrv. unfold cp_SR in ee.
  idtac "--------------------------------------------------------".
  idtac "Using hc_inversion:".
  Time inv_eval_expr m m'.
  (* Function spsr, get spsr from the current state *)
  apply (functions_behavior_ok e l b s vf0 fd0 m vargs0 t10 m3 vres0 l b s)
    in psrel; [idtac|exact Heqff0|exact ev_funcall].
  (* Function copy_StatusRegister, copy the current spsr to cpsr*)
  apply (functions_behavior_ok e l b s vf fd m3 vargs t2 m' vres l b
    (Arm6_State.set_cpsr s (Arm6_State.spsr s em))) in psrel;
  [idtac|exact Heqff|exact ev_funcall0].
  idtac "Qed:".
  exact psrel.
Time Qed.

(* ------------------------------------------------------------ *)
(* Use BasicElim to invert type eval_expr *)

Require Import Coq.Program.Equality.

Lemma same_cp_SR_basicelim :
  forall e m l b s t m' v em,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    eval_expression (Genv.globalenv prog_adc) e m cp_SR t m' v ->
    proc_state_related m' e
      (Ok tt (mk_semstate l b
      (Arm6_State.set_cpsr s (Arm6_State.spsr s em)))).
Proof.
  intros until em. intros psrel cpsr.
  inversion cpsr. subst. rename H into ee,H0 into esrv. unfold cp_SR in ee.
  clear cpsr.
  idtac "Using BasicElim:". 
  Time(
  try (repeat (generalize_eqs_vars ee; destruct ee; simplify_dep_elim));
  try (repeat (generalize_eqs_vars H; destruct H; simplify_dep_elim));
  try (repeat (generalize_eqs_vars H7; destruct H7; simplify_dep_elim));
  try (repeat (generalize_eqs_vars H6; destruct H6; simplify_dep_elim));
  try (repeat (generalize_eqs_vars H11; destruct H11; simplify_dep_elim));
  try (repeat (generalize_eqs_vars H8; destruct H8; simplify_dep_elim));
  try (repeat (generalize_eqs_vars H6; destruct H6; simplify_dep_elim));
  try (repeat (generalize_eqs_vars H8; destruct H8; simplify_dep_elim));
  try (repeat (generalize_eqs_vars H7; destruct H7; simplify_dep_elim))).  
  (* Function spsr, get spsr from the current state *)
  apply (functions_behavior_ok e l b s vf0 fd0 m vargs0 t4 m0 vres0 l b s)
    in psrel; [idtac|exact H12|exact H14].
  (* Function copy_StatusRegister, copy the current spsr to cpsr*)
  apply (functions_behavior_ok e l b s vf fd m0 vargs t3 m3 vres l b
    (Arm6_State.set_cpsr s (Arm6_State.spsr s em))) in psrel;
  [idtac|exact H3|exact H5].
  idtac "Qed:".
  exact psrel.
Time Qed.

Lemma print_the_end: True.
Proof.
  idtac "--------------------------------------------------------".  
  trivial.
Qed.

