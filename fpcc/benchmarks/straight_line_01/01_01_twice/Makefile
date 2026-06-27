.PHONY: fpcore pvs all

all: fpcore pvs

fpcore:
	fpcc --input 01_01_twice.c --backend fpcore

pvs:
	fpcc --input 01_01_twice.c --backend pvs --entry-point twice
