.PHONY: all fpcore pvs

all: fpcore pvs

fpcore:
	fpcc --input 01_07_sqroot.c --backend fpcore

pvs:
	fpcc --input 01_07_sqroot.c --backend pvs --entry-point sqroot

