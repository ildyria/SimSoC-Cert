/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010, 2011
 * LGPL license version 3 */

/* test the arm v6 instructions REV, REV16, REVSH
 * After 125 instructions executed, r0 should contain 2^4-1 = 15 */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)                         \
  if (COND) count+=index_; index_ <<= 1;

void arm_REV16(){
  uint32_t x=0;
    asm("rev16 %0, %1"
	:"=&r" (x)
	:"r" (0x12345678)
	);
    CHECK(x==0x34127856);
}

void arm_REV() {
  uint32_t x;
  asm("rev %0, %1"
      : "=&r" (x)
      : "r" (0x11223344));
  CHECK(x==0x44332211);
}

void arm_REVSH() {
  uint32_t x;
  asm("revsh %0, %1"
      : "=&r" (x)
      : "r" (0x8765));
  CHECK(x==0x6587);
}

void arm_REVSH_bis() {
  uint32_t x;
  asm("revsh %0, %1"
      : "=&r" (x)
      : "r" (0xcafe));
  CHECK(x==0xfffffeca);
}

int main() {
  arm_REV16();
  arm_REV();
  arm_REVSH();
  arm_REVSH_bis();
  return count;
}
