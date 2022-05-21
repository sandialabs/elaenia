# ACSL Syntax for Floating-Point

The goal of this is to put forth a draft document so we can agree on a
syntax and semantics for floating-point in ACSL. The goals of this
syntax should be, in decreasing priority:

1. Support specification of compositional floating-point error analysis
2. Be as simple as possible
3. Allow straightforward translation to floating-point automated reasoning tools
4. Be as similar as possible to existing FP syntax in ACSL

This is based on Section 2.2.5 of the Frama-C ACSL Implementation,
version 1.20 (Implementation in Frama-C version 29.0).

## Features in a Nutshell

Versus the current ACSL, we recommend four main new features:

1. `real numerics` and `floating numerics` to have local
   syntax, as opposed to a global description via `-wp-model +real` or
   `-wp-model +float`.
2. `\uncertainty` predicate. This allows to model sources of error
   external to Frama-C; i.e., from physical phenomena or other analysis
   from external tools. For example,

    ```
    /*@ requires 0.0 <= x <= 1000.0;
        requires \uncertainty(x,-5.0,5.0); */
    ```
3. `lower < x < upper` implies `\is_finite(x)`, to simplify the syntax.
4. `\ulp(x)` to represent the unit in the last place. We should agree on
   _which_ definition; I suggest the one chosen by ReFlow
   (https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=bc07e8d52dbbac5bef9551bbc111b95d82dc4766).

   `logic real ulp_dp(real x) = (x == 0)? \pow(BASE, (emin_dp - p_dp + 1)) :  \pow(BASE, (\max(\floor(\log(\abs(x))/\log(2)), emin_dp) - p_dp + 1));`

    ulp(x) = $2^{emin - p + 1}


## Syntax

### Floating-Point numbers vs Real Numbers

The default behavior for ACSL shall be _floating point_. If _real_ is desired, then one can write:

```
   /*@ real numerics */
```

versus

```
   /*@ floating numerics */
```

One can always disambiguate by either _casting_:

```
    /*@ \round_float(rounding_mode m, real x) */
```
or _casting_.  Casting from a C integer type or a float type to a float
or a double is as in C: the same conversion operations apply. For
example:

```
    /*@ real numerics;
        assert 0.1 + 0.2 == 0.3;
    */

    /*@ floating numerics;
        assert 0.1 + 0.2 != 0.3;
    */

    /*@ real numerics;
        assert (float) 0.1 + (float) 0.2 != (float) 0.3;
    */


    /*@ floating numerics;
        assert (real) 0.1 + (real) 0.2 == (real) 0.3;
    */
```

