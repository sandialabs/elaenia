#include <math.h>

typedef struct {
	double v[3]; } vec3;

/*@
  requires -1000.0 <= x.v[0] <= 1.000;
  requires -1000.0 <= x.v[1] <= 1.000;
  requires -1000.0 <= x.v[2] <= 1.000;

  requires -1000.0 <= y.v[0] <= 1.000;
  requires -1000.0 <= y.v[1] <= 1.000;
  requires -1000.0 <= y.v[2] <= 1.000;
*/
double dot_product(vec3 x, vec3 y)
{
	return x.v[0] * y.v[0] +
	       x.v[1] * y.v[1] +
	       x.v[2] * y.v[2];
}

/*@
  requires -1000.0 <= x.v[0] <= 1.000;
  requires -1000.0 <= x.v[1] <= 1.000;
  requires -1000.0 <= x.v[2] <= 1.000;
*/
double norm(vec3 x)
{
	return sqrt(x.v[0] * x.v[0] +
	       x.v[1] * x.v[1] +
	       x.v[2] * x.v[2]);
}

