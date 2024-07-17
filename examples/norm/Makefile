FCT := norm
WP := -wp -wp-rte -wp-no-warn-memory-model -wp-model +float -wp-fct $(FCT)

wp: norm.c
	frama-c $(WP) $^

norm: norm.c
	$(CC) -o $@ $^ -O3 -Wall -Wno-error=format-security -fstack-protector-all -lm -lpthread

clean:
	$(RM) norm *.o
