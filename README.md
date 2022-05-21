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

- examples - example functions for analysis. They are ordered in
  increasing complexity as follows
    1. 01_straightline - No control flow, no transcendentals.
    2. 02_transcend    - No control flow, transcendentals (sin, cos, sqrt)
    3. 03_vectors      - No control flow, but operations on vectors
    4. 04_matrices     - Operations on matrices
    5. 05_kalman       - Various Kalman filter examples

- acsl - Proposed language extensions for the ANSI C Specification
  Language (ACLS) to better support compositional floating-point
  reasoning.

## About

This work is funded by Sandia National Laboratories' Laboratory
Directed Research & Development (LDRD) program, project 24-1299:
"Automated Error Analysis of Numerical Kernels for High-Consequence
Systems with Frama-C" and project 25-0103: "Automated Error Analysis of
Numerical Software for High-Consequence Systems."


Sandia National Laboratories is a multimission laboratory managed and
operated by National Technology and Engineering Solutions of Sandia,
LLC., a wholly owned subsidiary of Honeywell International, Inc., for
the U.S. Department of Energy’s National Nuclear Security Administration
under contract DE-NA-0003525.

The name Elaenia is taken from the name of an album by a band called
Floating Points. It is also a kind of bird.
