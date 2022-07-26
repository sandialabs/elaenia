#include<limits.h>

/* Some notes for this spec:
 * Frama-C converts every float into reals. Next step is to determine whether
 *   the \exact and the \result actually differ using Frama-C's float model.
 * max double: 1.8e308
 * max int: 2.1e9
 * k <=~ 8.5e298, let's underapproximate to simplify
 * Make k whatever to make math easier
 * x      x + u/2    x + u
 * |---------|---------|
 * <----* round to nearest
 * Use 0x1p52 because we do not assume rounding mode
 */

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
  @ ensures \abs(\exact(\result) - \result) <= k*n*0x1p-52;
 */

double sum (double *x, int n, double k)
{
  int i;
  double acc = 0.0;
  /*@
    loop invariant 0 <= i < n;
    loop assigns i, acc;
    loop variant n-i;
  */
  for (i = 0; i < n; i++) {
    acc += x[i];
  }
  return acc;
}

