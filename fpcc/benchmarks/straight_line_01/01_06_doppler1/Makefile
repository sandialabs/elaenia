.PHONY: all fpcore pvs

all: fpcore pvs

fpcore:
	fpcc --input 01_06_doppler1.c --backend fpcore

pvs:
	fpcc --input 01_06_doppler1.c --backend pvs --entry-point doppler1

