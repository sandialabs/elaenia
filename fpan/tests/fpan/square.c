#include <stdio.h>

// the "ensures" error bound was computed with
// frama-c -eva tests/fpan/square.c -main square
/*@ requires 0.001 <= x && x <= 1000.;
  @ requires \is_finite(x);
  @ ensures 1.00000011116e-06 <= x <= 1000000.;
  @ ensures \old(errno) == errno;
  @ assigns \nothing;
 */
// TODO: Given `requires` clause, how can I generate `ensures` clause
// automatically, using, e.g. frama-c -eva?
float square(float x)
{
	return x*x;
}

int main(int argc, char *argv[])
{
	float t = 0.0009765625f;
	float x = square(t);
	printf("0.001    = %.10e (%a)\n"
	       "0.001^2  = %.10e (%a)\n", t, t, x, x);
	printf("0.000001 = %.10e (%a)\n", 0.000001f, 0.000001f);
	return 0;
}
