# It seems this has no effect: -wp-model +float

# May want a larger wp-steps (I've seen 1500 in test cases) # -wp-steps 1500
WP = -wp -wp-rte

DEBUG =
DEBUG ?= -wp-debug 3 -wp-verbose 3 -wp-print -wp-out log

GEN_WHYML =
GEN_WHYML ?= -wp-gen -wp-prover why3 -wp-msg-key="print-generated"

WP_PROVERS = alt-ergo,gappa,colibri2,z3

all: twice temp nmse333 determinant sin sqroot

.PHONY: twice temp nmse333 determinant sin sqroot

twice: 01_01_twice.c
	frama-c $(WP) -wp-model +float -wp-prover $(WP_PROVERS) $(GEN_WHYML) $(DEBUG) -wp-fct $@ $^

temp: 01_02_temp.fptaylor 01_02_temp.c
	frama-c $(WP) -wp-model +float -wp-prover $(WP_PROVERS) $(GEN_WHYML) $(DEBUG) -wp-fct $@ 01_02_temp.c
	fptaylor --opt=bb-eval 01_02_temp.fptaylor

nmse333: 01_03_nmse333.c
	@echo "todo"

determinant: 01_04_determinant.c
	@echo "todo"

doppler1: 01_06_doppler1.c
	@echo "todo"

sin: 01_05_sin.c
	@echo "todo"

sqroot: 01_07_sqroot.c
	frama-c $(WP) -wp-model +float -wp-prover $(WP_PROVERS) $(GEN_WHYML) $(DEBUG) -wp-fct $@ $^

debug: 01_07_sqroot.c
	gappa $^
	frama-c -wp -wp-rte -wp-gen -wp-prover why3 -wp-print -wp-msg-key="print-generated"  01_07_sqroot.c

