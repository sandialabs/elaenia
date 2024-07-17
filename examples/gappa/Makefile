# It seems this has no effect: -wp-model float
WP = -wp -wp-rte
DEBUG = -wp-debug 3 -wp-verbose 3 -wp-print -wp-out log
SRC = interval.c

.PHONY: twice
twice:
	frama-c $(WP) -wp-prover alt-ergo,gappa $(DEBUG) -wp-fct $@ $(SRC)


