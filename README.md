# FPan: Floating-Point Error Analysis in Frama-C

Floating-point error analysis plugin for frama-c using FPTaylor

## Building

### Prerequisites

This plugin requires some prerequisites, all of which can be installed
via `opam`. If you are building frama-c from source, you also need
`autoconf`.

```
opam update
opam install --deps-only frama-c
opam install ppx_import ppx_deriving gappa
why3 config detect # Detect provers; need only be done once

# Build and install the stable release of frama-c
opam install frama-c

# Or, you can build and install development version of frama-c
git clone https://git.frama-c.com/pub/frama-c.git
cd frama-c
autoconf
./configure --prefix=$HOME/.local
make -j8
make install
```

I also recommend installing [merlin](https://github.com/ocaml/merlin)
to add type checking and other IDE stuff for OCaml.

### Building

- `make` builds and expands.
- `make install` is how you use it 

## Usage

Tjj


