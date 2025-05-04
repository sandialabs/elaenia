# Notes for Compiling Examples

## Straightline
### Dependenies
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
