struct SLv6_MMU;
struct SLv6_Processor;
struct SLv6_StatusRegister;
struct SLv6_SystemCoproc;

struct SLv6_MMU {
  unsigned int begin;
  unsigned int size;
  unsigned int end;
  unsigned char *mem;
};

struct SLv6_Processor {
  struct SLv6_MMU *mmu_ptr;
  struct SLv6_StatusRegister cpsr;
  struct SLv6_StatusRegister spsrs[5];
  struct SLv6_SystemCoproc cp15;
  unsigned int id;
  unsigned int user_regs[16];
  unsigned int fiq_regs[7];
  unsigned int irq_regs[2];
  unsigned int svc_regs[2];
  unsigned int abt_regs[2];
  unsigned int und_regs[2];
  unsigned int *pc;
  unsigned char jump;
};

struct SLv6_StatusRegister {
  unsigned char N_flag;
  unsigned char Z_flag;
  unsigned char C_flag;
  unsigned char V_flag;
  unsigned char Q_flag;
  unsigned char J_flag;
  unsigned char GE0;
  unsigned char GE1;
  unsigned char GE2;
  unsigned char GE3;
  unsigned char E_flag;
  unsigned char A_flag;
  unsigned char I_flag;
  unsigned char F_flag;
  unsigned char T_flag;
  int mode;
  unsigned int background;
};

struct SLv6_SystemCoproc {
  unsigned char ee_bit;
  unsigned char u_bit;
  unsigned char v_bit;
};

unsigned char const __stringlit_6[71] = "ERROR: simulating something unpredictable (../arm6/simlight/adc.c:%d)\012";
unsigned char const __stringlit_3[49] = "!(new_pc&(inst_size(proc)-1)) && \042pc misaligned\042";
unsigned char const __stringlit_2[11] = "reg_id!=15";
unsigned char const __stringlit_4[14] = "pc misaligned";
unsigned char const __stringlit_5[81] = "ERROR: Current mode does not have a SPSR (../arm6/simlight/slv6_processor.h:%d)\012";
unsigned char const __stringlit_1[34] = "../arm6/simlight/slv6_processor.h";

extern unsigned char ConditionPassed(struct SLv6_StatusRegister *, int);
extern void copy_StatusRegister(struct SLv6_StatusRegister *, struct SLv6_StatusRegister *);
extern unsigned int *addr_of_reg_m(struct SLv6_Processor *, unsigned char, int);

unsigned int reg_m(struct SLv6_Processor *proc, unsigned char reg_id, int m)
{
  return *addr_of_reg_m(proc, reg_id, m);
}

void set_reg_m(struct SLv6_Processor *proc, unsigned char reg_id, int m, unsigned int data)
{
  *addr_of_reg_m(proc, reg_id, m) = data;
}

unsigned int reg(struct SLv6_Processor *proc, unsigned char reg_id)
{
  return reg_m(proc, reg_id, (*proc).cpsr.mode);
}

void set_reg(struct SLv6_Processor *proc, unsigned char reg_id, unsigned int data)
{
  reg_id != 15 ? (void) 0
    : __assert_fail(__stringlit_2, __stringlit_1, 58, (unsigned char *) 0);
  set_reg_m(proc, reg_id, (*proc).cpsr.mode, data);
}

unsigned int inst_size(struct SLv6_Processor *proc)
{
  return (*proc).cpsr.T_flag ? 2 : 4;
}

void set_pc_raw(struct SLv6_Processor *proc, unsigned int new_pc)
{
  (!(new_pc & inst_size(proc) - 1) ? (__stringlit_4 ? 1 : 0) : 0) ? (void) 0
    : __assert_fail(__stringlit_3, __stringlit_1, 68, (unsigned char *) 0);
  (*proc).jump = 1;
  *(*proc).pc = new_pc + 2 * inst_size(proc);
}

void set_reg_or_pc(struct SLv6_Processor *proc, unsigned char reg_id, unsigned int data)
{
  if (reg_id == 15) {
    set_pc_raw(proc, data);
  } else {
    set_reg(proc, reg_id, data);
  }
}

unsigned char CurrentModeHasSPSR(struct SLv6_Processor *proc)
{
  return (*proc).cpsr.mode < 5;
}

struct SLv6_StatusRegister *spsr(struct SLv6_Processor *proc)
{
  if (CurrentModeHasSPSR(proc)) {
    return &*((*proc).spsrs + (*proc).cpsr.mode);
  } else 
    ERROR("Current mode does not have a SPSR");
  abort();
}

unsigned char CarryFrom_add2(unsigned int a, unsigned int b)
{
  return a + b < a;
}

unsigned char CarryFrom_add3(unsigned int a, unsigned int b, unsigned int c)
{
  return CarryFrom_add2(a, b) ? 1 : (CarryFrom_add2(a + b, c) ? 1 : 0);
}

unsigned char OverflowFrom_add2(unsigned int a, unsigned int b)
{
  unsigned int r;
  r = a + b;
  return ((a ^ ~b) & (a ^ r)) >> 31;
}

unsigned char OverflowFrom_add3(unsigned int a, unsigned int b, unsigned char c)
{
  return OverflowFrom_add2 (a, b) || OverflowFrom_add2 (a + b, c);
}

unsigned char get_bit(unsigned int x, unsigned int n)
{
  return x >> n & 1;
}
