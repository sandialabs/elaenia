/* This code is a way to test various floating-point analyses using frama-c.
 * Run frama-c analysis with any of
 *   make
 *   make norm
 *   make eva
 * Some questions:
 * - Can we do interval arithmetic in Frama-C? (A: Yes, with gappa, though
 *   to discover the error bounds requires using it externally)
 * - In the second (unused) ACSL specification, is there a way to avoid
 *   wrapping \is_finite around each subexpression in norm?
 *   (A: no, but this may be a feature in the future).
 */

#ifdef __FRAMAC__
#include "__fc_builtin.h"
#endif

#include <stdio.h>
#include <math.h>

typedef union {
  double ijk[3];
  struct { double i, j, k; } v;
} Vector_3;


/*@ predicate valid_vect(Vector_3* a) =
  \valid_read(a) && \is_finite(a->v.i) && \is_finite(a->v.j) && \is_finite(a->v.k);
*/

/*@ requires valid_vect(a) && valid_vect(b);
  @ requires -1000.0 <= a->v.i && a->v.i <= 1000.0;
  @ requires -1000.0 <= a->v.j && a->v.j <= 1000.0;
  @ requires -1000.0 <= a->v.k && a->v.k <= 1000.0;
  @ requires -1000.0 <= b->v.i && b->v.i <= 1000.0;
  @ requires -1000.0 <= b->v.j && b->v.j <= 1000.0;
  @ requires -1000.0 <= b->v.k && b->v.k <= 1000.0;
  @ assigns \nothing;
  @ ensures -3000000.0 <= \result && \result <= 3000000.0;
*/
double dot(Vector_3* a, Vector_3* b)
{
  return a->v.i*b->v.i + a->v.j*b->v.j + a->v.k*b->v.k;
}


/* // This spec can prove without Gappa
  @ requires \valid_read(a);
  @ requires \is_finite(a->v.i);
  @ requires \is_finite(a->v.j);
  @ requires \is_finite(a->v.k);
  @ requires
  @   \let i2  = (double)(a->v.i * a->v.i);
  @   \let j2  = (double)(a->v.j * a->v.j);
  @   \let k2  = (double)(a->v.k * a->v.k);
  @   \let ij2 = (double)(i2 + j2);
  @   \let ijk2 = (double)(ij2 + k2);
  @   \is_finite(i2) && \is_finite(j2) && \is_finite(k2) &&
  @     \is_finite(ij2) && \is_finite(ijk2);
  @ assigns errno;
  @ ensures \is_finite(\result);
  @ ensures \result >= 0.0;
  @ ensures errno == \old(errno);
*/
/*@ // This spec requires Gappa
  @ requires \valid_read(a);
  @ requires valid_vect(a);
  @ requires -1000.0 <= a->v.i && a->v.i <= 1000.0;
  @ requires -1000.0 <= a->v.j && a->v.j <= 1000.0;
  @ requires -1000.0 <= a->v.k && a->v.k <= 1000.0;
  @ assigns errno;
  @ ensures \is_finite(\result);
  @ ensures 0.0 <= \result <= 1732.051;
  @ ensures errno == \old(errno);
*/
double norm(Vector_3* a)
{
  return sqrt(a->v.i*a->v.i + a->v.j*a->v.j + a->v.k*a->v.k);
}

/* Nondeterministically generate vectors */
#ifdef __FRAMAC__
double fc_main(void)
{
  double i1 = Frama_C_double_interval(-1000.0,1000.0);
  double j1 = Frama_C_double_interval(-1000.0,1000.0);
  double k1 = Frama_C_double_interval(-1000.0,1000.0);
  double i2 = Frama_C_double_interval(-1000.0,1000.0);
  double j2 = Frama_C_double_interval(-1000.0,1000.0);
  double k2 = Frama_C_double_interval(-1000.0,1000.0);
  Vector_3 x =  {{i1, j1, k1}};
  Vector_3 y =  {{i2, j2, k2}};
  return dot(&x, &y);
}
#endif


int main(void)
{
  double d;
  Vector_3 x =  {{.1, -.2, .3}};
  Vector_3 y =  {{.3, .3, .1}};
  d = dot(&x,&y);

  x.v.i = x.v.j = x.v.k = 1000.0;
  y.v.i = y.v.j = y.v.k = -1000.0;
  d = dot(&x,&x);
  printf("x . x = %.16e (%a)\n", d, d);

  d = dot(&x,&y);
  printf("x . y = %.16e (%a)\n", d, d);
}
