# Makefile for fpan plugin.
# load - loads plugin using frama-c

# Set up options
FRAMAC_SHARE := $(shell frama-c-config -print-share-path)
PLUGIN_NAME = FPan
PLUGIN_CMO = fpan_finder fpan_driver 
# PLUGIN_TESTS_DIRS := fpan
include $(FRAMAC_SHARE)/Makefile.dynamic

SOURCES = $(PLUGIN_CMO:.cmo=.ml) $(PLUGIN_CMO:.cmo=.mli) $(PLUGIN_NAME).mli

load: $(SOURCES)
	frama-c -load-module top/FPan

list: $(SOURCES)
	frama-c -load-module top/FPan -plugins

help: $(SOURCES)
	frama-c -load-module top/FPan -fpan-help

fpan: $(SOURCES)
	frama-c -load-module top/FPan -fpan

verbose: $(SOURCES)
	frama-c -load-module top/FPan -fpan -fpan-verbose 2

test: $(SOURCES) tests/fpan/add.c
	make
	frama-c -load-module top/FPan -fpan -fpan-verbose 2 tests/fpan/add.c

eva: tests/fpan/square.c
	frama-c -eva tests/fpan/square.c -main square
	frama-c -eva tests/fpan/sterbenz.c -main sterbenz

WP_PROVER = z3,cvc4,alt-ergo,gappa
WP_OPT = -wp-rte -wp-prover $(WP_PROVER) -wp-timeout 10
wp: tests/fpan/square.c tests/fpan/sterbenz.c
	frama-c -wp $(WP_OPT) -wp-fct square $^
	frama-c -wp $(WP_OPT) -wp-fct sterbenz $^
