# FPTaylor Why3 Plug-In

Based off the DAHCS Late-Start LDRD "Automated Error Analysis of Numerical Kernels for High-Consequence Systems with Frama-C" #24-1299

## Dependencies

- opam (install using your favorite package manager, or https://opam.ocaml.org/doc/Install.html)
  + If installing for the first time, run `opam init`, then get the
    files into your path via `eval $(opam env)` (or put a line into your
    rc file as opam instructs).
- why3 (install via opam install why3)
- stow
- make (on MacOS)
- fptaylor (https://github.com/soarlab/FPTaylor)
  + Ocaml Num (`opam install num`)
  + z3 (`<pkg manager> install z3`)
  + `git clone git@github.com:soarlab/FPTaylor.git`
  + `make fptaylor-simple-interval`
  + `export FPTAYLOR_BASE=$(pwd)`
  + If you want this on your path, copy somewhere both `fptaylor` then run `echo "export FPTAYLOR_BASE=$(pwd)" >> ~/.bashrc` (to the correct rc file)

## Building

`make` - this compiles the code (in `_build`), then makes an `install`
directory and a `fptaylor.install` file including all the necessary
libraries.

## Running

`./run_why3.sh` - this makes the `install` directory visible to why3, then
runs why3

