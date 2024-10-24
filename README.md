# Nerif: Automated Error Analysis of Numerical Software for High-Consequence Systems

This work is funded by Sandia National Laboratories' Laboratory
Directed Research & Development (LDRD) program, project 24-1299:
"Automated Error Analysis of Numerical Kernels for High-Consequence
Systems with Frama-C" and project 25-0103: "Automated Error Analysis of
Numerical Software for High-Consequence Systems."

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

Nerif is the name of a playable character (Oracle) in the computer game
Dota 2.  Without stretching an analogy too much, Nerif floats and keeps
you safe.  Likewise, this project is about keeping you safe while using
floating point.

