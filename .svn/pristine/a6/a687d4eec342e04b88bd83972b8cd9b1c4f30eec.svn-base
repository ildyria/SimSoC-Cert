# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

FILES := adc_compcert projection my_inversion

VFILES := $(FILES:%=%.v)

COQ_INCLUDES := -I $(DIR)/coq -I $(DIR)/arm6

include $(DIR)/Makefile.coq
