# It seems this has no effect: -wp-model +float

# May want a larger wp-steps ("A machine-independent alternative to timeout",
# I've seen 1500 in test cases)
# -wp-steps 1500
WP = -wp -wp-rte

DEBUG =
DEBUG ?= -wp-debug 3 -wp-verbose 3 -wp-print -wp-out log

GEN_WHYML =
GEN_WHYML ?= -wp-gen -wp-prover why3 -wp-msg-key="print-generated"

WP_PROVERS = alt-ergo,gappa,colibri2,z3

all: twice sqroot sqroot_2nd temp nmse333 determinant sin

.PHONY: twice sqroot sqroot_2nd temp nmse333 determinant sin

# Listed in order of increasing complexity
twice: twice.c
	frama-c $(WP) -wp-model +float -wp-prover $(WP_PROVERS) $(GEN_WHYML) $(DEBUG) -wp-fct $@ $^

sqroot_2nd: sqroot_2nd.c
	frama-c $(WP) -wp-model +float -wp-prover $(WP_PROVERS) $(GEN_WHYML) $(DEBUG) -wp-fct $@ $^

sqroot: sqroot.c
	frama-c $(WP) -wp-model +float -wp-prover $(WP_PROVERS) $(GEN_WHYML) $(DEBUG) -wp-fct $@ $^

temp: temp.fptaylor temp.c
	frama-c $(WP) -wp-model +float -wp-prover $(WP_PROVERS) $(GEN_WHYML) $(DEBUG) -wp-fct $@ temp.c
	fptaylor --opt=bb-eval temp.fptaylor

sqroot_debug: sqroot.c
	gappa $^
	frama-c -wp -wp-rte -wp-gen -wp-prover why3 -wp-print -wp-msg-key="print-generated" $^

nmse333: 01_03_nmse333.c
	@echo "todo"

determinant: 01_04_determinant.c
	@echo "todo"

doppler1: 01_06_doppler1.c
	@echo "todo"

sin: 01_05_sin.c
	@echo "todo"

