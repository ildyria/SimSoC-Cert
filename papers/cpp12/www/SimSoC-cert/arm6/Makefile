# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

######################################################################
# compile Coq files

DIR := ..

FILES := Message Config Functions SCC Exception Proc State Simul

VFILES := Arm6.v $(FILES:%=Arm6_%.v) Arm6_Inst.v Arm6_Dec.v

COQ_INCLUDES := -I $(DIR)/coq

include $(DIR)/Makefile.coq

