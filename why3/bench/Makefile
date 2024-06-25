BENCHMARKS = 01_add 02_div 03_sinOrder3 04_sinOrder3_ens
ANALYSIS = $(BENCHMARKS:=.out)
CFG = bench.cfg

all: $(ANALYSIS)

$(ANALYSIS): %.out : %.fptaylor
	fptaylor -c $(CFG) $< > $@

# $(BENCHMARKS): % : %.fptaylor
# 	fptaylor -c $(CFG) $<

.PHONY: clean
clean:
	$(RM) $(ANALYSIS)
	$(RM) -r log tmp
