# ImpToFunc

This shows an example of translating from an imperative language into a
functional language. As of now, there is an implementation which
generates PVS code for use as input to PRECiSA, but because of
versioning and Haskell challenges, this is currently accomplished by
pasting in the PVS AST used by PRECiSA. This is not license compatible,
since NASA's open source license is not GPL compatible.  Until this is
fixed, you may contact Sam Pollard for a copy of this code which
translates from `IMP` to `PVS`.


## Building

Make sure you have Haskell stack installed, then run

`stack build`

## Running

```
stack exec ImpToFunc-exe -- --translate test/input.imp
```

Will create a file called `input-trans.func`.

```
stack exec ImpToFunc-exe -- test/input.imp
```

Will execute the imperative function.

