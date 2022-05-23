# Makefile for fpan plugin.
# load - loads plugin using frama-c

load: fpan.ml
	frama-c -load-script $<

register: fpan.ml
	frama-c -load-script $< -plugins

help: fpan.ml
	frama-c -load-script $< -fpan-help

fpan: fpan.ml
	frama-c -load-script $< -fpan

verbose: fpan.ml
	frama-c -load-script $< -fpan -fpan-verbose 2

.PHONY: clean
clean:
	$(RM)
