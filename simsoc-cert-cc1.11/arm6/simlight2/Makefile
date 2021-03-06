# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

COQ_INCLUDES := -I $(DIR)/coq

include $(DIR)/Makefile.common

default: simlight

######################################################################
# compilation of simlight

CPPFLAGS := #-I$(DIR)/tools/bin2elf
CFLAGS := -Wall -Wextra -Wno-unused -Werror -g #-fprofile-arcs -ftest-coverage
#CC := ccomp -fstruct-assign -fno-longlong
LDFLAGS :=
LIBRARIES := #-lgcov

SOURCES_MO := common.c elf_loader.c arm_mmu.c arm_system_coproc.c slv6_math.c \
	slv6_mode.c slv6_status_register.c arm_not_implemented.c \
	slv6_processor.c slv6_condition.c

SOURCES := $(SOURCES_MO) slv6_iss.c slv6_iss_printers.c

HEADERS := $(DIR)/tools/bin2elf/elf.h \
	int64_init.h int64_config.h int64_native.h int64_emul.h \
	$(SOURCES_MO:%.c=%.h) \
	slv6_iss_c_prelude.h slv6_iss_h_prelude.h  \
	slv6_iss.h slv6_iss_printers.h \
	slv6_iss_expanded.h slv6_iss_grouped.h

EXTRA_SOURCES := slv6_iss_arm_decode_exec.c slv6_iss_arm_decode_store.c \
              slv6_iss_thumb_decode_exec.c slv6_iss_thumb_decode_store.c \
              slv6_iss_expanded.hot.c  slv6_iss_grouped.hot.c \
              slv6_iss_expanded.cold.c slv6_iss_grouped.cold.c

OBJECTS := $(SOURCES:%.c=%.o) $(EXTRA_SOURCES:%.c=%.o) simlight.o

GENFILES_MO := slv6_iss_expanded.hot.c  slv6_iss_grouped.hot.c \
            slv6_iss_expanded.cold.c slv6_iss_grouped.cold.c \
            slv6_iss_expanded.h slv6_iss_grouped.h \
            slv6_iss.h print_sizes.c \
            slv6_iss_arm_decode_exec.c slv6_iss_arm_decode_store.c \
            slv6_iss_thumb_decode_exec.c slv6_iss_thumb_decode_store.c \
            slv6_iss-llvm_generator.hpp slv6_iss_printers.c \
            slv6_iss_printers.h slv6_iss_printers.cpp \
            slv6_iss_printers.hpp

GENFILES := $(GENFILES_MO) slv6_iss.c

simlight: $(OBJECTS)
	$(CC) $(LDFLAGS) $^ -o simlight $(LIBRARIES)

%.o: %.c $(HEADERS)
	$(CC) -c $(CPPFLAGS) $(CFLAGS) $< -o $@

$(GENFILES): $(SIMGEN) ../arm6.pc ../arm6.syntax ../arm6.dec
	$(SIMGEN) -v -oc4dt slv6_iss -ipc ../arm6.pc \
		-isyntax ../arm6.syntax -idec ../arm6.dec \
		-iwgt simsoc.wgt

$(GENFILES_MO): slv6_iss.c

../arm6.pc ../arm6.dec ../arm6.syntax: FORCE
	$(MAKE) -C .. $(@:../%=%)

simlight.opt: FORCE
	gcc simlight.c $(SOURCES:%=--include %) -g -DNDEBUG -O3 -I../elf -o $@

clean::
	rm -f $(OBJECTS) $(GENFILES) simlight simlight.opt *.gcda *.gcno
	rm -rf simlight.opt.dSYM

######################################################################
# representation of simlight in Coq

.PHONY: proof

proof: libcoq all.vo

all.vo: $(DIR)/coq/Cnotations.vo

.PRECIOUS: all.v

all.c: $(HEADERS) $(SOURCES) $(EXTRA_SOURCES) simlight.c
	cat $+ | sed -e 's|#include "\(.*\)|//#include "\1|' -e 's|#include <elf.h>|//#include <elf.h>|' > $@

clean::
	rm -f all.c all.v all.glob all.vo

######################################################################
# extraction

ocaml: extraction-libcoq extraction
	$(SHOW) ocamlbuild arm6/simlight2/extraction/all.cmo
	$(HIDE) $(OCAMLBUILD) arm6/simlight2/extraction/all.cmo

extraction.v: all.vo

######################################################################
# dependency graph

simlight.dep: FORCE
	grep '#include ' $(HEADERS) $(SOURCES) $(EXTRA_SOURCES) simlight.c | sed -e 's|#include||' -e 's|["<>]||g' -e 's|\([^/]*\)/||g' > $@

clean::
	rm -f simlight.dep

.PHONY: depend

depend: simlight.ps
	gv $< &
