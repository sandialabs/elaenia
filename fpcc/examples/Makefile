CC ?= gcc

# Make sure you have PVS_LIBRARY_PATH set
# export PVS_LIBRARY_PATH="$PVS_LIBRARY_PATH:$(realpath ../external/PRECiSA/PVS/)"
# I have the extra nasalibs at ../PVS/nasalib

sqroot:
	stack run fpcc -- --input $@.c --backend pvs --entry-point $@
	precisa $@.pvs $@.input
	# Currently fails:
	# proveit sqroot_cert.pvs sqroot_num_cert.pvs sqroot_real.pvs

dot_product: dot_product.c
	$(CC) $< -c -lm
	stack run fpcc -- --input $@.c --backend pvs --entry-point dot_product
	stack run fpcc -- --input $@.c --backend pvs --entry-point norm
	precisa $@.pvs $@.input

pmic: pmic.c
	$(CC) $< -c
	stack run fpcc -- --input $@.c --backend pvs --entry-point calc_vsys


.PHONY: clean
clean:
	$(RM) *.input *.pvs *.func *.o

