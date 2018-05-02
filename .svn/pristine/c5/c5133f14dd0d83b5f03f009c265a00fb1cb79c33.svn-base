# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := .

MAKE := make

.PHONY: all

all:
	$(MAKE) -C coq
	$(MAKE) -C arm6
	$(MAKE) -C hc_inversion
	@echo "For testing times: cd hc_inversion; make time"
	@echo "for testing sizes: cd hc_inversion; make size"

SUBDIRS := coq arm6 hc_inversion

clean::
	rm -f *~
	@for d in $(SUBDIRS); do make -C $$d $@; done
	rm -f compcert dir-locals.el hc_inversion/.dir-locals.el coqrc
