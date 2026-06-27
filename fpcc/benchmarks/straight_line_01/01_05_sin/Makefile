.PHONY: all fpcore pvs

all: fpcore pvs

fpcore:
	fpcc --input 01_05_sin.c --backend fpcore

pvs:
	fpcc --input 01_05_sin.c --backend pvs --entry-point sin_dbl

