WHY3_DATADIR=$(shell why3 --print-datadir)
WHY3_LIBDIR=$(shell why3 --print-libdir)
PLUGIN=fptaylor

# need `main` to be before `link_why3_libs` so that the appropriate directory
# structures get set up before `stow` links in the why3 install files
all: main link_why3_libs

.PHONY: link_why3_libs
link_why3_libs:
	mkdir -p install/lib/why3
	mkdir -p install/share/why3
	stow --target=install/lib/why3 --dir=$(WHY3_LIBDIR) .
	stow --target=install/share/why3 --dir=$(WHY3_DATADIR) .

.PHONY: main
main:
	dune build @install -p $(PLUGIN)
	dune install --prefix ./install $(PLUGIN)

.PHONY: clean
clean:
	dune clean
	rm -rf ./install && true
