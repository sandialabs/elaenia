# It seems this has no effect: -wp-model float
WP = -wp -wp-rte
DEBUG = -wp-debug 3 -wp-verbose 3 -wp-print -wp-out log

all: twice temp

.PHONY: twice temp
twice: 01_01_twice.c
	frama-c $(WP) -wp-prover alt-ergo,gappa $(DEBUG) -wp-fct $@ $^

temp: 01_02_temp.fptaylor
	fptaylor $^
