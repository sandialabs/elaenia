# It seems this has no effect: -wp-model +float

# May want a larger wp-steps (I've seen 1500 in test cases) # -wp-steps 1500
WP = -wp -wp-rte

DEBUG =
DEBUG ?= -wp-debug 3 -wp-verbose 3 -wp-print -wp-out log

GEN_WHYML =
GEN_WHYML ?= -wp-gen -wp-prover why3 -wp-msg-key="print-generated"

all: twice temp nmse333 determinant sin sqroot

.PHONY: twice temp nmse333 determinant sin sqroot

twice: 01_01_twice.c
	frama-c $(WP) -wp-model +float -wp-prover alt-ergo,gappa,colibri2 $(GEN_WHYML) $(DEBUG) -wp-fct $@ $^

temp: 01_02_temp.fptaylor
	@echo "todo"
	# fptaylor $^

nmse333: 01_03_nmse333.c
	@echo "todo"

determinant: 01_04_determinant.c
	@echo "todo"

doppler1: 01_06_doppler1.c
	@echo "todo"

sin: 01_05_sin.c
	@echo "todo"

sqroot: 01_07_sqroot.c
	@echo "todo"

