.PHONY: all fpcore pvs

all: fpcore pvs

fpcore:
	fpcc --input 01_04_determinant.c --backend fpcore

pvs:
	fpcc --input 01_04_determinant.c --backend pvs --entry-point determinant_dbl

