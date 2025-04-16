This is a static analysis tool for analyzing the floating point error in
numerical C code.  It is based upon abstract interpretation and uses the novel
abstract domain of step functions to represent the floating point error.

# Dependencies
First, install OCaml (version 4.13 or greater) from
[here](https://ocaml.org/install).

You will need [CIL](https://github.com/goblint/cil) and ocaml rounding
modes installed:

```
opam pin add -y round git@github.com:tyabu12/ocaml-round.git
opam install goblint-cil round
```

# Running

The tool ingests a C file and a "specification file".  Examples can be found in
the `c` directory.  

Run with `dune exec -- <C-FILE> -f <FUN> -sf <SPEC-FILE> -out <OUT-FILE> -<FORMAT>`.
Replace `<C-FILE>` with the file you want to analyze, `<FUN>` with the function
you are analyzing, `<SPEC-FILE>` with the specification file, `<OUT-FILE>`
with the filename where the output will be written, and `<FORMAT>` with the
output format (either `csv` or `acsl`.  Examples of invocations
can be found in the makefile.

The specification file format is a list of variable bounds such as:
```
x = {([2;4], 0.001), ([4;8], 0.0001)}
y = {([1;3], 0.003), ([3;6], 0.0003)}
```
The above declares the bounds for two variables, each with two different
segments.  `x`'s value is between 2 and 8, with two different errors
associated with different regions of the interval. 

The performance of the analyzer depends on how granular the analysis is.  You
can limit the number of segments per variable with the `-ensures-intervals
<NUM>` flag.  The default it 10,000 intervals.


## Output
The tool can either output a csv file or
[ACSL](https://frama-c.com/html/acsl.html). 

Each row in the CSV contains the variable, an interval for the value of that
variable and a maximum error bound for the interval.

The outputted ACSL will contain an overall interval for the value of the
variable (in an ensures clause) as well as error bounds that cover the
interval in behavior clauses.  The ACSL comment is above the C declaration of
the function.


## Make Targets
The make file has a few targets.  The default behavior is to `clean`, `test`,
and `run`.
- `build` : Builds the project.
- `clean` : removes build files.
- `test` : Runs the test suite.
- `run` : Runs the analyzer on a selection of tests from the `c/` directory
  with csv output. 
- `test-acsl` : Runs the analyzer on a selection of tests from the `c/`
  directory with acsl output.
- `test-intervals` : Runs the analyzer on a selection of tests from the `c/`
  directory with a limit on the amount of intervals.

