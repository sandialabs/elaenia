# Makefile for fperror plugin.
# load - loads plugin using frama-c

load: fperror.ml
	frama-c -load-script $^

.PHONY: clean
clean:
	$(RM)
