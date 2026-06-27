FPCC    ?= stack run fpcc --
PRECISA ?= precisa

BUILD := build

FUNCS := doppler1 rigidBody1 rigidBody2 jetEngine turbine1 turbine2 turbine3 \
         verhulst predatorPrey carbonGas sqroot sineOrder3 bspline3

BOUNDS := $(addprefix $(BUILD)/,$(addsuffix .bound,$(FUNCS)))

.PHONY: all acsl analyze clean

all: analyze

# Run by hand to convert FPCore :pre preconditions to ACSL
acsl:
	$(FPCC) --pre-to-acsl --input rosa.c --output rosa.acsl.c

analyze: $(BOUNDS)

$(BUILD)/%.bound: rosa.acsl.c | $(BUILD)
	cp rosa.acsl.c $(BUILD)/$*.c
	$(FPCC) --input $(BUILD)/$*.c --backend pvs --entry-point $*
	cd $(BUILD) && $(PRECISA) $*.pvs $*.input | tee $*.bound

$(BUILD):
	mkdir -p $(BUILD)

clean:
	$(RM) -r $(BUILD)
