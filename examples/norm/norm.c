/* A simple 2-d vector norm and its ACSL specification.
 * Written by Geoff Hulette, modified by Samuel Pollard */
#include <math.h>

typedef struct {
    double x;
    double y;
} Vec;

/*@ requires \valid_read(v);
  @ requires \is_finite(v->x);
  @ requires \is_finite(v->y);
  @ requires
  @     \let x2  = (double)(v->x * v->x);
  @     \let y2  = (double)(v->y * v->y);
  @     \let xy2 = (double)(x2 + y2);
  @     \is_finite(x2) && \is_finite(y2) && \is_finite(xy2);
  @ assigns errno;
  @ ensures \is_finite(\result);
  @ ensures \result >= 0.0;
  @ ensures errno == \old(errno);
*/
double norm(Vec *v)
{
    return sqrt(v->x * v->x + v->y * v->y);
}

int main()
{
    Vec x = {.1, .1};    
    double n = norm(&x);
    return (n < 0.0);
}
