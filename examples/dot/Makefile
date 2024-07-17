# It seems this has no effect: -wp-model float
WP = -wp -wp-rte -wp-no-warn-memory-model
#DEBUG = -wp-debug 3 -wp-verbose 3
SRC = dot.c

.PHONY: fc-dot norm clean
fc-dot:
	frama-c $(WP) -wp-prover alt-ergo,gappa $(DEBUG) -wp-fct dot $(SRC)

norm:
	frama-c $(WP) -wp-prover alt-ergo,gappa $(DEBUG) -wp-fct norm $(SRC)

eva:
	frama-c -eva -main fc_main $(SRC)

dot: dot.c
	$(CC) -o $@ $^ -O3 -Wall -fstack-protector-all -Wno-error=format-security -lm -lpthread

clean:
	$(RM) dot *.o

