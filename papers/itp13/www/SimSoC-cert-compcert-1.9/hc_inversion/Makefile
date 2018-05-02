# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

CMPFILES := comparison_hcinv comparison_inv comparison_derinv comparison_basicelim

FILES := adc_compcert projection hcinv_eval_expr $(CMPFILES)

BAR := echo "--------------------------------------------------------"

VFILES := $(FILES:%=%.v) -custom '@$(BAR); echo Sizes; du -b $(CMPFILES:%=%.vo); $(BAR) ' "$(FILES:%=%.vo)" asksize

COQ_INCLUDES := -I $(DIR)/coq -I $(DIR)/arm6

include $(DIR)/Makefile.coq

#############################################################################
# show size of .vo files

.PHONY: size

size:  $(CMPFILES:%=%.vo)
	@$(BAR) ; du -b $+ ; $(BAR)

time:
	@rm -f comparison_times.vo
	@make comparison_times.vo

#############################################################################
