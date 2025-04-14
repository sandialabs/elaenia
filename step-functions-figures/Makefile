SRC=$(wildcard exact/*.c)
CSVS = $(wildcard data/*-mine.csv)
PYTHON = python3
#PYTHON = ipython3 -i

# For homebrew
# brew install gmp mpfr
# brew link gmp mpfr
# export LIBRARY_PATH="$LIBRARY_PATH:$(brew --prefix)/lib"
# export C_INCLUDE_PATH="$C_INCLUDE_PATH:$(brew --prefix)/include"

all: run analyze

run: build
	@echo "running..."
	./out/compare.o

analyze: setup sin rigidBody1 rigidBody2 sqroot turbine1 turbine2 cav10 verhulst bspline3 doppler1 predatorPrey

rigidBody1:
	$(PYTHON) analysis/analysis.py data/$@.csv data/$@-mine.csv $@ false r   true linear nolegend nocolorbar
rigidBody2:
	$(PYTHON) analysis/analysis.py data/$@.csv data/$@-mine.csv $@ false r   true linear nolegend nocolorbar

sqroot:
	$(PYTHON) analysis/analysis.py data/$@.csv data/$@-mine.csv $@ false ret true linear nolegend nocolorbar

turbine1:
	$(PYTHON) analysis/analysis.py data/$@.csv data/$@-mine.csv $@ false ret true linear nolegend nocolorbar

turbine2:
	$(PYTHON) analysis/analysis.py data/$@.csv data/$@-mine.csv $@ false ret true linear nolegend nocolorbar
bspline3:
	$(PYTHON) analysis/analysis.py data/$@.csv data/$@-mine.csv $@ false ret true linear nolegend nocolorbar
doppler1:
	$(PYTHON) analysis/analysis.py data/$@.csv data/$@-mine.csv $@ false r   true linear nolegend nocolorbar
predatorPrey:
	$(PYTHON) analysis/analysis.py data/$@.csv data/$@-mine.csv $@ false ret true linear nolegend nocolorbar
cav10:
	$(PYTHON) analysis/analysis.py data/$@.csv data/$@-mine.csv $@ false tmp true log nolegend nocolorbar bi
	mv results/$@-error-cmp.pdf results/$@-error-cmp-bi.pdf
	$(PYTHON) analysis/analysis.py data/$@.csv data/$@-mine.csv $@ false tmp true log nolegend nocolorbar

verhulst:
	$(PYTHON) analysis/analysis.py data/$@.csv data/$@-mine.csv $@ false ret true linear 'upper left' colorbar

sin:
	$(PYTHON) analysis/analysis.py data/sin/sin-data.csv data/sin/sin-mine-good.csv sin true x false linear best colorbar
	$(PYTHON) analysis/analysis.py data/$@-exp.csv data/sin/sin-mine-good.csv $@ false x   true linear nolegend nocolorbar
	mv results/sin-error-cmp.pdf results/sin-error-cmp-small.pdf
	$(PYTHON) analysis/analysis.py data/sin/sin-data.csv data/sin/sin-mine-good.csv sin false x true linear best colorbar
	mv results/sin-error-cmp.pdf results/sin-error-cmp-large.pdf

setup:
	@echo "analyzing..."
	mkdir -p results

#$(PYTHON) analysis/analysis.py data/matmul-exp.csv data/matmul-mine.csv matmul false c[0]
#$(PYTHON) analysis/analysis.py data.csv data/determinant.csv determinant false r
#$(PYTHON) analysis/analysis.py data.csv data/branch/branch-simple-instable-mine.csv branch false z
#$(PYTHON) analysis/analysis.py data.csv data/branch/branch-simple-data-mine.csv branch false z
#$(PYTHON) analysis/analysis.py data/branch/branch.csv data/branch/branch-mine.csv branch false z
#$(PYTHON) analysis/analysis.py data/branch/branch-exp.csv data/branch/branch-instable-mine.csv branch false r

build: $(SRC)
	@echo "building..."
	mkdir -p out
	gcc -g -DN=1000000 -o out/compare.o $^ -lmpfr -lgmp

clean:
	$(RM) out/compare.o

.PHONY: clean build analyze run $(CSVS)
FORCE: ;
