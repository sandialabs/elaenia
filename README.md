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
- examples - example functions for analysis. They are ordered in
  increasing complexity as follows
    1. 01_straightline - No control flow, no transcendentals.
    2. 02_transcend    - No control flow, transcendentals (sin, cos, sqrt)
    3. 03_

## Building

### Linux
- The usual thing should work for a reasonable version of ocamlc

### MacOS
- Tested on ocamlc 5.2.0
- `git clone git@github.com:sampollard/FPTaylor.git --branch why3`
- `make fptaylor-simple-interval`
- `cp -r fptaylor b_and_b <install-dir>`
