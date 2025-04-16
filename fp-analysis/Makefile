all: test run

run: clean
	#dune exec --profile release -- analyzer -f main c/kalman/kettle.c -sf c/kalman/kettle.spec
	#dune exec --profile release -- analyzer -f foo c/simple-array-test.c -sf c/simple-array-test.spec
	#dune exec --profile release -- analyzer -f axb_33 c/bench/matmul3x3.c -sf c/bench/matmul3x3.spec
	#dune exec --profile release -- analyzer -f ex7 c/bench/nmse_3_3_3.c -sf c/bench/nmse_3_3_3.spec
	# ---------------
	# ROSA benchmarks
	dune exec --profile release -- analyzer -f doppler1 c/rosa/rosa.c -sf c/rosa/doppler1.spec -out doppler1.csv -csv
	dune exec --profile release -- analyzer -f rigidBody1 c/rosa/rosa.c -sf c/rosa/rigidBody1.spec -out rigidBody1.csv -csv
	dune exec --profile release -- analyzer -f rigidBody2 c/rosa/rosa.c -sf c/rosa/rigidBody2.spec -out rigidBody2.csv -csv
	dune exec --profile release -- analyzer -f turbine1 c/rosa/rosa.c -sf c/rosa/turbine1.spec -out turbine1.csv -csv
	dune exec --profile release -- analyzer -f turbine2 c/rosa/rosa.c -sf c/rosa/turbine2.spec -out turbine2.csv -csv
	dune exec --profile release -- analyzer -f turbine3 c/rosa/rosa.c -sf c/rosa/turbine3.spec -out turbine3.csv -csv
	dune exec --profile release -- analyzer -f verhulst c/rosa/rosa.c -sf c/rosa/verhulst.spec -out verhulst.csv -csv
	dune exec --profile release -- analyzer -f predatorPrey c/rosa/rosa.c -sf c/rosa/predatorPrey.spec -out predatorPrey.csv -csv
	dune exec --profile release -- analyzer -f carbonGas c/rosa/rosa.c -sf c/rosa/carbonGas.spec -out carbonGas.csv -csv
	dune exec --profile release -- analyzer -f sqroot c/rosa/rosa.c -sf c/rosa/sqroot.spec -out sqroot.csv -csv
	dune exec --profile release -- analyzer -f sineOrder3 c/rosa/rosa.c -sf c/rosa/sineOrder3.spec -out sineOrder3.csv -csv
	dune exec --profile release -- analyzer -f cav10 c/rosa/rosa.c -sf c/rosa/cav10.spec -out cav10.csv -csv
	dune exec --profile release -- analyzer -f bspline3 c/rosa/rosa.c -sf c/rosa/bspline3.spec -out bspline3.csv -csv

test-acsl: clean
	dune exec --profile release -- analyzer -f doppler1 c/rosa/rosa.c -sf c/rosa/doppler1.spec -out doppler1.acsl -acsl
	dune exec --profile release -- analyzer -f foo c/simple-array-test.c -sf c/simple-array-test.spec -out simple-array-test.acsl -acsl

test-intervals: clean
	dune exec --profile release -- analyzer -f doppler1 c/rosa/rosa.c -sf c/rosa/doppler1.spec -out doppler1.acsl -acsl -ensures-intervals 10
	dune exec --profile release -- analyzer -f foo c/simple-array-test.c -sf c/simple-array-test.spec -out simple-array-test.acsl -acsl -ensures-intervals 10


test: clean
	dune exec --profile release -- analyzer -test

clean:
	dune clean

build:
	dune build
