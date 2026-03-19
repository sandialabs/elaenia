# Notes and Instructions

## Compiling a Sqrt constant
- [This stack overflow](https://stackoverflow.com/questions/21808271/why-do-square-roots-of-constants-known-at-compile-time-not-require-linking-the-m)
  indicates `sqrt` constants get expanded compile-time (with MPFR)

- But a bigger question is: how can I mark things as not usable or to
  skip analysis?
  + Do this by changing #defines

- For variadic, similar story. You may replace the .c file with stubs,
  or with Frama-C just not include the .c file (only the .h).

## Solutions
- You can rewrite it to not be `static`, but this is less efficient.
- Or you can #define your way out of it and pass `-DDO_FRAMA_C` into
  frama-c.
- Or you can write a little program to compute it:
```
#include <math.h>
#include <stdio.h>
int main()
{
printf("%.15e\n", expr);
}
```
Then replace the expression as necessary.
