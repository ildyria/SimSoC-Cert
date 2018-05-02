
void ADC(struct SLv6_Processor *proc, unsigned char S, int cond, unsigned char d, unsigned char n, unsigned int shifter_operand)
{
  unsigned int old_Rn;
  unsigned int old_CPSR;
  old_Rn = reg(proc, n);
  old_CPSR = (*proc).cpsr;
  if (ConditionPassed(&(*proc).cpsr, cond)) {
    set_reg_or_pc(proc, d, old_Rn + shifter_operand + old_CPSR.C_flag);
    if (S == 1 ? (d == 15 ? 1 : 0) : 0) {
      if (CurrentModeHasSPSR(proc)) {
        copy_StatusRegister(&(*proc).cpsr, spsr(proc));
      } else 
        unpredictable();
    } else {
      if (S == 1) {
        (*proc).cpsr.N_flag = get_bit(reg(proc, d), 31);
        (*proc).cpsr.Z_flag = reg(proc, d) == 0 ? 1 : 0;
        (*proc).cpsr.C_flag =
          CarryFrom_add3(old_Rn, shifter_operand, old_CPSR.C_flag);
        (*proc).cpsr.V_flag =
          OverflowFrom_add3(old_Rn, shifter_operand, old_CPSR.C_flag);
      }
    }
  }
}


