BENCHMARKS = 01_add 02_div 03_sinOrder3 04_sinOrder3_ens
FPTAYLOR = $(BENCHMARKS:=.out)
C_SOURCES = $(BENCHMARKS:=.c)
WP_REAL = $(BENCHMARKS:=.wp-real)
WP_FLOAT = $(BENCHMARKS:=.wp-float)
CFG = bench.cfg

all: $(FPTAYLOR) wp

$(FPTAYLOR): %.out : %.fptaylor
	fptaylor -c $(CFG) $< > $@

.PHONY: wp
wp: $(WP_REAL) $(WP_FLOAT)

$(WP_REAL): %.wp-real : %.c
	frama-c -wp -wp-rte -wp-model +real -wp-prover=alt-ergo,z3 $< -wp-print > $@

$(WP_FLOAT): %.wp-float : %.c
	frama-c -wp -wp-rte -wp-model +float -wp-prover=alt-ergo,z3 $< -wp-print > $@

# $(BENCHMARKS): % : %.fptaylor
# 	fptaylor -c $(CFG) $<

.PHONY: clean
clean:
	$(RM) $(FPTAYLOR) $(WP_REAL) $(WP_FLOAT)
	$(RM) -r log tmp
