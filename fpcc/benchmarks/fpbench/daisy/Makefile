.PHONY: all fpcore pvs

all: fpcore pvs

fpcore:
	fpcc --input cartesian_to_polar_radius.c --backend fpcore
	fpcc --input cartesian_to_polar_theta.c --backend fpcore

pvs:
	fpcc --input cartesian_to_polar_radius.c --backend pvs --entry-point code
	fpcc --input cartesian_to_polar_theta.c --backend pvs --entry-point code

