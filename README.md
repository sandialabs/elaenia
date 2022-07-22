# FPan: Floating-Point Error Analysis in Frama-C

Floating-point error analysis plugin for frama-c using FPTaylor

## Building

### Prerequisites

This plugin requires some prerequisites, all of which can be installed
via `opam`. If you are building frama-c from source, you also need
`autoconf`. I recommend installing frama-c-fpan inside the frama-c
source tree so that merlin can get its type annotations (this also
requires building frama-c).

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

# It is also convenient to have the .merlin files to help with type annotations etc.
make merlin

mv <location of this repository> frama-c/src/plugins
```

I also recommend installing [merlin](https://github.com/ocaml/merlin)
to add type checking and other IDE stuff for OCaml. I recommend cloning
this repo inside the `frama-c/src/plugins` directory if only because
merlin will work better.

### Building

- `make` builds the plugin, and stores it in `top`.
- (Not stable) `make install` is how you install it on your system; it
  installs in the same place that frama-c libraries are installed, so
  you have to be able to write to there. With opam, this would be in
  `~/.opam/switch/share/frama-c` (or something like that).
- `make verbose` will run the help option, printing some diagnostics

## Usage

- `make wp` will run the weakest-precondition analysis for the test
  files.
- `make eva` will run (to get the ensures clauses, at first) for the
  tests.
- `make test` will run the analysis for the `tests/fpan/` directory.
  Currently does not do much, but is a good way to check that
  _something_ gets executed.

## Some advice on Development

A useful guide to CIL is
[here](https://people.eecs.berkeley.edu/~necula/cil/api/Cil.html).

## Roadmap
We want to have some code with a requires clause, generate the correct
input, then "discover" the output (the ensures clause). Ways to do
this: use FPTaylor, eva, or Gappa. This step should be sound, so every
transformation which is done ideally has a proof.


The first step of this is to generate _a_ FPTaylor script given a C
floating-point program. For example, computing the square of the 2-norml
of a five-dimensional vector, subject to the following, looks like:
```
/* 
/*@ requires \valid_read(x + (0 .. 4));
  @ requires \forall integer i; 0 <= i < 5 ==>
  @     \is_finite(x[i]) &&
  @     0.001 <= x[i] <= 1000.0 &&
  @     0.001 <= y[i] <= 1000.0;
*/
norm2 = 0.0;
for (i=0; i<5; i++) {
   dot += x[i]*x[i];
}
```

becomes this in FPTaylor

```
Variables
	real x_0 in [0.001, 1000.0],
	real x_1 in [0.001, 1000.0],
	real x_2 in [0.001, 1000.0],
	real x_3 in [0.001, 1000.0],
	real x_4 in [0.001, 1000.0]
;
Definitions
	s_1 rnd64 = x_0 * x_0,
	s_2 rnd64 = s_1 + x_1 * x_1,
	s_3 rnd64 = s_2 + x_2 * x_2,
	s_4 rnd64 = s_3 + x_3 * x_3,
	s_5 rnd64 = s_4 + x_4 * x_4,
;
Expressions
	norm2 = s_5,
;
```
You can see how this will get out of hand for any reasonable
floating-point program. The goal, then, is to have this be compressed
into _just_ the error for `s_5`, so we can calculate the range and error
for `dot_5`, thus compressing the analysis.


The next step would be to do a code transformation on the C program,
replacing a bounded summation with just the result of the sum. For
example,

```
/*@ requires \valid_read(x + (0 .. n-1));
  @ requires \is_finite(k) && 0.0 <= k && k <= 1e200;
  @ requires \forall integer i; 0 <= i < n ==>
  @     \is_finite(x[i]) &&
  @     -k <= x[i] <= k  &&
  @     \round_error(x[i]) == 0.0;
  @ requires 0 < n && n <= INT_MAX;
  @ assigns \nothing;
  @ ensures \is_finite(\result);
  @ ensures \result == \sum(0,n-1,\lambda integer i; x[i]);
  @ ensures \abs(\exact(\result) - \result) <= k*n*0x1p-52
 */

double sum (double *x, int n, double k)
{
  int i;
  double acc = 0.0;
  for (i = 0; i < n; i++) {
    acc += x[i];
  }
  return acc;
}
```

Currently, Mohit is working on proving this in `coq/sum.c`.
Where the result would just be all of the `ensures` clauses, converted
into FPTaylor.

### Some issues
- The goal was to have the pretty-printer output a comment for each
  line that is relevant (read: analyzable) with FPTaylor, then print it
  as a comment, followed by the corresponding FPTaylor expression. This
  would require some rewriting, since the pretty-printer for annotations
  already includes line breaks. I asked this question to
  [stackoverflow](https://stackoverflow.com/questions/72496160/pretty-printing-with-a-comment-string-prefixing-a-box)
  and got a nice answer, but I haven't implemented this yet.

## Structure of an FPTaylor Input File
A complete guide is given
[here](https://github.com/soarlab/FPTaylor/blob/develop/REFERENCE.md).

An FPTaylor file is divided up into five portions, each containing
a comma-separated list of statements and ending with a semicolon.

```
// Here is a line comment
Constants
  list stmt,
;
Variables
  list stmt,
;
Definitions
  list stmt,
;
Constraints
  list stmt,
;
Expressions
  list stmt,
;
```

Only `Variables` and `Expressions` are required.
