/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test arm v6 new instructions:   CPY CPS PKHBT PKHTB SEL SETEND
 * After 554 instructions executed, r0 should contain 2^16-1 = 0xffff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count +=index_; index_ <<= 1;

int GE0(uint32_t cpsr) {return (cpsr>>16)&1;}
int GE1(uint32_t cpsr) {return (cpsr>>17)&1;}
int GE2(uint32_t cpsr) {return (cpsr>>18)&1;}
int GE3(uint32_t cpsr) {return (cpsr>>19)&1;}
int GE10(uint32_t cpsr) {return (cpsr>>16)&3;}
int GE32(uint32_t cpsr) {return (cpsr>>18)&3;}
int M_flag(uint32_t cpsr){return cpsr&0x1f;}
int A_flag(uint32_t cpsr){return (cpsr>>8)&1;}
int I_flag(uint32_t cpsr){return (cpsr>>7)&1;}
int F_flag(uint32_t cpsr){return (cpsr>>6)&1;}

/* Copy is a pre-UAL synonym for MOV (register). */
void arm_CPY() {
  uint32_t x1,x2,x3,x4;
  asm("cpy %0, %1\n\t"
      : "=&r" (x1)
      : "r" (0x10101010));
  asm("cpy %0, %1\n\t"
      : "=&r" (x2)
      : "r" (0x1010101));
  asm("cpy %0, %1\n\t"
      : "=&r" (x3)
      : "r" (0x0));
  asm("cpy %0, %1\n\t"
      : "=&r" (x4)
      : "r" (0xffffffff));
  CHECK((x1 == 0x10101010));
  CHECK((x2 == 0x1010101));
  CHECK((x3 == 0x0));
  CHECK((x4 == 0xffffffff));
}

/* Change Processor State is available only in privileged modes. It changes one or more of the A, I, and F */
/* interrupt disable bits and the mode bits of the CPSR, without changing the other CPSR bits. */
void arm_CPS() {
  uint32_t f1,f2;

  asm("cpsid aif, #31\n\t"
      "mrs %0, CPSR"
      : "=&r" (f1)
      );
  
  asm("cpsie aif, #31\n\t"
      "mrs %0, CPSR"
      : "=&r" (f2)
      );
  CHECK((M_flag(f1) == 31)&&(A_flag(f1) == 1)&&(I_flag(f1) == 1)&&(F_flag(f1) == 1));
  CHECK((M_flag(f2) == 31)&&(A_flag(f2) == 0)&&(I_flag(f2) == 0)&&(F_flag(f2) == 0));
}

/* Pack Halfword combines one halfword of its first operand with the other halfword of its shifted second */
/* operand. */
void arm_PKHBT() {
  uint32_t x;
  asm("pkhbt %0, %1, %2, lsl #1\n\t"
      
      : "=&r" (x)
      : "r" (0x0000ffff), "r" (0xffff0000));
  CHECK((x == 0xfffeffff));
}
void arm_PKHTB() {
  uint32_t x=0;
  asm("pkhtb %0, %1, %2, asr #1\n\t"
      
      : "=&r" (x)
      : "r" (0xff000000), "r" (0xff00));
  CHECK((x == 0xff007f80));
}

/* Select Bytes selects each byte of its result from either its first operand or its second operand, according to */
/* the values of the GE flags. */
void arm_SEL() {
  uint32_t x,ge,result;
  asm("sadd8 %2, %5, %6\n\t"
      "sel %0, %3, %4\n\t"
      "mrs %1, cpsr\n\t"
      : "=&r" (x), "=&r" (ge), "=&r" (result)
      : "r" (0x12345678), "r" (0x87654321), "r" (0x026080fe), "r" (0x0360fffe));
  CHECK((x == 0x12344321));
  CHECK(GE3(ge)==1);
  CHECK(GE2(ge)==1);
  CHECK(GE1(ge)==0);
  CHECK(GE0(ge)==0);
  CHECK((result==0x05c07ffc));
}

/* Set Endianness writes a new value to ENDIANSTATE. */
void arm_SETEND_BE(){
  uint32_t f;
    asm("setend be\n\t"
	"mrs %0, cpsr"
	:"=&r" (f)
	);
    f=(f&(1<<9))>>9;
    CHECK((f == 1));
}
void arm_SETEND_LE(){
  uint32_t f;
    asm("setend le\n\t"
	"mrs %0, cpsr"
	:"=&r" (f)
	);
    f=(f&(1<<9))>>9;
    CHECK((f == 0));
}

int main() {
  arm_CPY();
  arm_CPS();
  arm_PKHBT();
  arm_PKHTB();
  arm_SEL();
  arm_SETEND_BE();
  arm_SETEND_LE();
  return count;
}
