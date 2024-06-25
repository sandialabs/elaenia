# FPTaylor Why3 Plug-In 

This work is funded by Sandia National Laboratories' Laboratory
Directed Research & Development (LDRD) program, project 24-1299:
"Automated Error Analysis of Numerical Kernels for High-Consequence
Systems with Frama-C"

## Structure of this Repository
- fpan - a bare-bones Frama-C plug-in, standing for "FP analyzer" - we
  determined this was not the right way to solve the problem because of
  the existing support for floating-point in Why3, and that would allow
  us to leverage the existing power of WP. and so...
- why3 - the Why3 plug-in directory.

## Building

### Linux
- The usual thing should work for ocamlc < 5.0

### MacOS
- Tested on ocamlc 5.2.0
- `git clone git@github.com:sampollard/FPTaylor.git --branch why3`
- `make fptaylor-simple-interval`
