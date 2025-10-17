# It seems this has no effect: -wp-model float
WP = -wp -wp-rte -wp-no-warn-memory-model

# More info
WP_DEBUG ?= -wp-debug 3 -wp-verbose 3
# Super Debug
# WP_DEBUG += -wp-print
# Mega Debug
# WP_DEBUG += -wp-gen -wp-prover why3 -wp-msg-key="print-generated" -wp-out logs

.PHONY: wp-dot wp-dot_union eva-dot_union wp-norm

dot: dot.c
	$(CC) -o $@ $^

wp-dot: dot.c
	frama-c $(WP) -wp-prover z3,alt-ergo,gappa $(WP_DEBUG) -wp-model +real -wp-fct dot $^

dot_union: dot_union.c
	$(CC) -o $@ $^ -O3 -Wall -fstack-protector-all -Wno-error=format-security -lm

wp-dot_union: dot_union.c
	frama-c $(WP) -wp-prover z3,alt-ergo,gappa $(WP_DEBUG) -wp-fct dot $^

eva-dot_union: dot_union.c
	frama-c -eva -main fc_main $^

norm: norm.c
	$(CC) -o $@ $^ -O3 -Wall -Wno-error=format-security -fstack-protector-all -lm -lpthread

wp-norm: norm.c
	frama-c -wp -wp-rte -wp-no-warn-memory-model -wp-model +float -wp-fct norm norm.c

mean-var: mean-var.c
	$(CC) -o $@ $^

.PHONY: clean
clean:
	$(RM) dot dot_union norm mean-var *.o .frama-c

