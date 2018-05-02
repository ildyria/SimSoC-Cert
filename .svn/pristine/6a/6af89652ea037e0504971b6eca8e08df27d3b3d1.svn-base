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

Lemma same_cp_SR :
  forall e m l b s t m' v em,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    eval_expression (Genv.globalenv prog_adc) e m cp_SR t m' v ->
    proc_state_related m' e
      (Ok tt (mk_semstate l b
      (Arm6_State.set_cpsr s (Arm6_State.spsr s em)))).
Proof.
  intros until em. intros psrel cpsr.
  inversion cpsr. subst. rename H into ee,H0 into esrv. unfold cp_SR in ee.
  (*
  Time (inv_call m m';
        intros t1_ m1_ rf'_ t2_ m2_ rargs'_ vf_ vargs_ targs_ tres_ fd_ t3_ 
          vres_;
        intros ev_ex ev_elst esr1 eslst Heqcf Heqff Heqtf 
          ev_funcall esr2).
  Time (inv_valof m m1_; intros).
  Time (inv_var m m1_; intros).
  inv_cons m m2_; intros. 
  Time (inv_addrof m m; intros).*)
  inv_eval_expr m m'.
  (* Function spsr, get spsr from the current state *)
  apply (functions_behavior_ok e l b s vf0 fd0 m vargs0 t9 m3 vres0 l b s)
    in psrel; [idtac|exact Heqff0|exact ev_funcall].
  (* Function copy_StatusRegister, copy the current spsr to cpsr*)
  apply (functions_behavior_ok e l b s vf fd m3 vargs t2 m' vres l b
    (Arm6_State.set_cpsr s (Arm6_State.spsr s em))) in psrel;
  [idtac|exact Heqff|exact ev_funcall0].
  exact psrel.
Qed.
  
