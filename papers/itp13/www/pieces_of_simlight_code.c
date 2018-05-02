/* ------------------------------------------------------------------ */
/*
This file contains pieces of C code from simlight, our 
simulator for the ARM instruction set, which is itself 
a part of the SimSoC project [1].
Filenames refered to, such as slv6_status_register.h,
are for the authors usage only.

The main data structure in the simulator is SLv6_Processor,
representing the state of the processor. First we need
to define SLv6_StatusRegister, for representing the state
of a set of registers.
ARM contains 2 such sets, called CPSR and SPSR.

Several functions for manipulating these data structures
are available, including copy_StatusRegister provided below.

Next we give the C code for simulating the ADC instruction,
in order to say where is the code targeted by Lemma same_cp_SR 
considered in the paper.

Actually this lemma is useful not only ADC, but for the many 
instructions which contain the corresponding statement.

[1] F. Blanqui, C. Helmstetter, V. Joloboff, J.-F. Monin, and X. Shi. 
Designing a CPU model: from a pseudo-formal document to fast code. 
In Proceedings of the 3rd Workshop on Rapid Simulation and Performance 
Evaluation: Methods and Tools, Heraklion, Greece, January 2011.

*/

/* ------------------------------------------------------------------ */
/* DATA STRUCTURES */

/* --------------------------------- */
/* Defined in slv6_status_register.h */

struct SLv6_StatusRegister {
  bool N_flag; /* bit 31 */
  bool Z_flag;
  bool C_flag;
  bool V_flag; /* bit 28 */
  bool Q_flag; /* bit 27 */
  bool J_flag; /* bit 24 */
  bool GE0; /* bit 16 */
  bool GE1;
  bool GE2;
  bool GE3; /* bit 19 */
  bool E_flag; /* bit 9 */
  bool A_flag;
  bool I_flag;
  bool F_flag;
  bool T_flag; /* bit 5 */
  SLv6_Mode mode;
  uint32_t background; /* reserved bits */
};

extern void copy_StatusRegister(struct SLv6_StatusRegister *dst,
                                struct SLv6_StatusRegister *src);

/* --------------------------- */
/* Defined in slv6_processor.h */

struct SLv6_Processor {
  struct SLv6_MMU *mmu_ptr;
  struct SLv6_StatusRegister cpsr;
  struct SLv6_StatusRegister spsrs[5];
  struct SLv6_SystemCoproc cp15;
  size_t id;
  uint32_t user_regs[16];
  uint32_t fiq_regs[7];
  uint32_t irq_regs[2];
  uint32_t svc_regs[2];
  uint32_t abt_regs[2];
  uint32_t und_regs[2];
  uint32_t *pc; /* = &user_regs[15] */

  /* true if last instruction modified the pc; must be cleared after each step */
  bool jump;
};

/* ------------------------------------------------------------------ */
/* C FUNCTIONS */

/* -------------------------------------- */
/* This is the function for updating CPSR */
/* Defined in slv6_statusregister.c       */


void copy_StatusRegister(struct SLv6_StatusRegister *dst,
                         struct SLv6_StatusRegister *src) {
  dst->background = src->background;
  dst->N_flag = src->N_flag;
  dst->Z_flag = src->Z_flag;
  dst->C_flag = src->C_flag;
  dst->V_flag = src->V_flag;
  dst->Q_flag = src->Q_flag;
  dst->J_flag = src->J_flag;
  dst->GE0 = src->GE0;
  dst->GE1 = src->GE1;
  dst->GE2 = src->GE2;
  dst->GE3 = src->GE3;
  dst->E_flag = src->E_flag;
  dst->A_flag = src->A_flag;
  dst->I_flag = src->I_flag;
  dst->F_flag = src->F_flag;
  dst->T_flag = src->T_flag;
  dst->mode = src->mode;
}


/* --------------------------------------------------- */
/* One of the many functions using copy_StatusRegister */
/* This one is for simulating ADC instruction          */
/* (Add with Carry)                                    */
/* Defined in slv6_iss.c                               */

/* ADC */
void ADC(struct SLv6_Processor *proc,
    const bool S,
    const SLv6_Condition cond,
    const uint8_t d,
    const uint8_t n,
    const uint32_t shifter_operand)
{
  const uint32_t old_Rn = reg(proc,n);
  if (ConditionPassed(&proc->cpsr, cond)) {
    set_reg_or_pc(proc,d,((old_Rn + shifter_operand) + proc->cpsr.C_flag));
    if (((S == 1) && (d == 15))) {
      if (CurrentModeHasSPSR(proc))
        /* Here is the C instruction targeted by same_cp_SR */
        copy_StatusRegister(&proc->cpsr, spsr(proc));
      else
        unpredictable();
    } else {
      if ((S == 1)) {
        proc->cpsr.N_flag = get_bit(reg(proc,d),31);
        proc->cpsr.Z_flag = ((reg(proc,d) == 0)? 1: 0);
        proc->cpsr.C_flag = CarryFrom_add3(old_Rn, shifter_operand, proc->cpsr.C_flag);
        proc->cpsr.V_flag = OverflowFrom_add3(old_Rn, shifter_operand, proc->cpsr.C_flag);
      }
    }
  }
}

/* ----------------- */
/* Here we focus on: */

   copy_StatusRegister(&proc->cpsr, spsr(proc))

/* The Coq definition for the corresponding AST is:

For Compcert 1.9:

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


For Compcert 1.11:

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


*/
