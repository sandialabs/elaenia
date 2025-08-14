# Elaenia: Automated Error Analysis of Numerical Software for High-Consequence Systems

This repository provides tools and techniques for automated
floating-point error analysis of C programs with the goal of making it
easier to specify and verify behavior of numerics-heavy C programs, with
a focus on embedded systems.

## Structure of this Repository

This project began with exploration into a Frama-C plug-in. We soon
realized that the ReFlow project provides better opportunities for
improvement rather than writing our own Frama-C plug-ins. This is now
maintained as a fork for [ReFlow](https://github.com/nasa/reflow).

- `examples` - example functions for analysis. They are ordered in
  increasing complexity as follows
    1. 01_straightline - No control flow, no transcendentals.
    2. 02_transcend    - No control flow, transcendentals (sin, cos, sqrt)
    3. 03_vectors      - No control flow, but operations on vectors
    4. 04_matrices     - Operations on matrices
    5. 05_kalman       - Various Kalman filter examples

- `acsl` - Proposed language extensions for the ANSI C Specification
  Language (ACLS) to better support compositional floating-point
  reasoning.


- `fp-analysis` - This is the accompanying code for [1]. At some point, this
  may be integrated into the preprocessing step for building
  specifications of C code functions, or as an abstract interpretation
  framework for numerical C. But currently, it is a standalone OCaml
  utility.

  [1] Anthony Dario and Samuel D. Pollard. A Step-Function Abstract Domain for Granular Floating-Point Error Analysis. In _Proceedings of the 10th ACM SIGPLAN International Workshop on Numerical and Symbolic Abstract Domains (NSAD ’24)_, October 22, 2024, Pasadena, CA, USA. ACM, New York, NY, USA, 8 pages. [url](https://doi.org/10.1145/3689609.3689997) [pdf](https://sampollard.github.io/research/artifacts/dario_fp_nsad24.pdf)

- `roulette-stdlib` - This is unrelated to floating-point error
  analysis, but for administrative reasons is funded under this
  project. This work was done by Noam Steiner Tomer at a summer
  internship at Sandia developing a standard library of routines
  for [Roulette](https://dl.acm.org/doi/abs/10.1145/3729334).
  (Technical report to appear).

## About

This work is funded by Sandia National Laboratories' Laboratory
Directed Research & Development (LDRD) program, projects 24-1299:
"Automated Error Analysis of Numerical Kernels for High-Consequence
Systems with Frama-C", and projects 25-0103 and 26-1164: "Automated
Error Analysis of Numerical Software for High-Consequence Systems."

Sandia National Laboratories is a multimission laboratory managed and
operated by National Technology and Engineering Solutions of Sandia,
LLC., a wholly owned subsidiary of Honeywell International, Inc., for
the U.S. Department of Energy’s National Nuclear Security Administration
under contract DE-NA-0003525.

The name Elaenia is taken from the name of an album by a band called
[Floating Points](https://en.wikipedia.org/wiki/Elaenia_(album).
It is also a kind of bird.

