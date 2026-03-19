# Notes for Compiling Examples

These are (roughly) in order of increasing complexity.

## (01) Straightline

This provides lots of straighline examples. This was made during a time
where many different floating-point error analysis tools were used so
it's kind of a smattering of different "hello world" examples for the
various tools (PVS, FPTaylor, Frama-C, Gappa, Herbie, and even some
plotting)

### Dependencies
Note that these are the ones which are known to work. However, other versions should work, as long as they're supported by the correct versions of Why3 (for provers) and Rocq (for VST and Rocq libraries).

- ocamlc 4.14.2
- Frama-C (tested with v28.0)
- alt-ergo 2.4.2
- colibri2 0.4
- gappa 1.4.1
- z3 4.8.12
- CompCert 3.15
- Coq 8.19.2

Install with
```
opam init
eval $(opam env)
# Rocq/Coq
opam repo add rocq-released https://rocq-prover.org/opam/released
# Frama-C
<pkg-mgr> install z3
# Install all at once to let the opam figure dependencies and versions out
opam install frama-c alt-ergo colibri2 gappa coq-vst-lib coq-vst coq-vcfloat 
why3 config detect
```

### If you're using VSCode
- `opam install vscoq-language-server`

## (02) Tricky

These are some tricky examples (with just scalars) which are difficult
to analyze. These may not be priorities for verification but just know
that people do write things like this on occasion

## (03) Vectors

C examples with simple vectors of statically-known length.

## (04) Matrices

Examples of matrices.
- `matrix-int` is matrix-matrix multiplication with integers, proven in
  Frama-C (by Stephen Siegel).
- `matrix`: contains matrix and quaternion math, a basic implementation
  in C.
- `lu`: LU Decomposition in C.  Contains a VST proof of matrix-matrix
  multiplication written in Rocq by TJ Machado.
