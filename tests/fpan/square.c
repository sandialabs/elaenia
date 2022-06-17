#include <stdio.h>

/*@ requires 0.001 <= x && x <= 1000.;
  @ ensures 1.00000011116e-06 <= \result && \result <= 1000000.;
  @ ensures \old(errno) == errno;
 */
// TODO: Given `requires` clause, how can I generate `ensures` clause
// automatically, using, e.g. frama-c -eva?
double square(float x)
{
	return x*x;
}

int main(int argc, char *argv[])
{
	float t = 0.001f;
	float x = square(t);
	printf("0.001    = %.10e (%a)\n"
	       "0.001^2  = %.10e (%a)\n", t, t, x, x);
	printf("0.000001 = %.10e (%a)\n", 0.000001f, 0.000001f);
	return 0;
}
