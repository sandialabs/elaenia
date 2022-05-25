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

- `make` builds the plugin, and stores it in `top`.
- (Not stable) `make install` is how you install it on your system; it
  installs in the same place that frama-c libraries are installed, so
  you have to be able to write to there. With opam, this would be in
  `~/.opam/switch/share/frama-c` (or something like that).
- `make verbose` will run the help option, printing some diagnostics

## Usage

- `make test` will run the analysis for the `tests/fpan/` directory.
  Currently does not do much, but is a good way to check that
_something_ gets executed.
