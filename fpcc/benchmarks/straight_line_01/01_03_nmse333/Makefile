.PHONY: all fpcore pvs

all: fpcore pvs

fpcore:
	fpcc --input 01_03_nmse333.c --backend fpcore

pvs:
	fpcc --input 01_03_nmse333.c --backend pvs --entry-point nmse

