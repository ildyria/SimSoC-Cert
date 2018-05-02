# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := .

include $(DIR)/Makefile.common

default:
	$(MAKE) -C coq

.PHONY: all

all:
	$(MAKE) -C arm6

SUBDIRS := coq arm6 my_inversion

clean::
	ocamlbuild -no-links -clean
	@for d in $(SUBDIRS); do make -C $$d $@; done
