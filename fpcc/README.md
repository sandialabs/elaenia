# FPCC

## Installation

### Prerequisites:

- The usual `*nix` utilities: `make`, `wget`, `curl`, `git`,
- `cmake>=3.12`
- a C99/C++17 compiler.
- [Kodiak](https://github.com/nasa/Kodiak.git)
- [Haskell stack](https://docs.haskellstack.org/en/stable/)
  + `curl -sSL https://get.haskellstack.org/ | sh`
- To certify PRECiSA certificates:
  + [PVS version 8.0](http://pvs.csl.sri.com/)
  + [NASA PVS library](https://github.com/nasa/pvslib)

### Building

```
git submodule update --init --remote --recursive
./setup.sh
# Follow instructions
stack build
```

### Usage

```
stack run fpcc -- examples/sqroot.c
```

This will generate a file called `examples/sqroot.pvs`.

You may then generate a PVS certificate to check via `precisa`,
then verify the proof certificate using PVS:

```
precisa examples/sqroot.pvs examples/sqroot.input
pvs -batch examples/sqroot_num_cert.pvs examples/sqroot_real.pvs
```

### Troubleshooting

- The most likely causes of issues are the incorrect linking of Kodiak and
  FILIB. Make sure those are compiled and their environment variables set.

- Another likely cause of issues is the ghc version. While stack should
  handle all this for you, you may also consider using `ghcup` to
  install ghc 9.6.7

- If you cannot find precisa, make sure it is on your path. It
  installs to `$HOME/.cabal/bin`.

- If you see an error
  `dyld[54985]: symbol not found in flat namespace '__ZNSt8ios_base4InitD1Ev'`
  Or something similar, rebuilding Kodiak with GCC seemed to solve the
  issue (not Apple's Clang aliases to GCC)

- `[S-7011] While building package precisa-4.0.4 (scroll up to its section to see the error) using: ...`
  Make sure you have `extra-lib-dirs` at the end of your stack.yaml.

