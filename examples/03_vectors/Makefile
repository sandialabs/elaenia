# It seems this has no effect: -wp-model float
WP = -wp -wp-rte -wp-no-warn-memory-model
#DEBUG = -wp-debug 3 -wp-verbose 3

.PHONY: fc-dot norm clean
fc-dot: dot.c
	frama-c $(WP) -wp-prover alt-ergo,gappa $(DEBUG) -wp-fct dot dot.c

dot: dot.c
	$(CC) -o $@ $^ -O3 -Wall -fstack-protector-all -Wno-error=format-security -lm -lpthread

eva:
	frama-c -eva -main fc_main dot.c

norm: norm.c
	$(CC) -o $@ $^ -O3 -Wall -Wno-error=format-security -fstack-protector-all -lm -lpthread

fc-norm: norm.c
	frama-c -wp -wp-rte -wp-no-warn-memory-model -wp-model +float -wp-fct norm norm.c

clean:
	$(RM) dot *.o

