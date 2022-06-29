#include <stdio.h>

// the "ensures" error bound was computed with
// frama-c -eva tests/fpan/square_ptr.c -main square
/*@ requires \valid_read(x);
  @ requires 0.001 <= *x && *x <= 1000.;
  @ ensures 1.00000011116e-06 <= \result && \result <= 1000000.;
  @ ensures \old(errno) == errno;
  @ assigns \nothing;
 */
// TODO: Given `requires` clause, how can I generate `ensures` clause
// automatically, using, e.g. frama-c -eva?
// TODO: Ensure that *x doesn't point to errno
float square_ptr(const float *x)
{
	return (*x)*(*x);
}

// TODO: Look into proving separated
/*@ requires \separated(x[0..n], y[0..n]);
 */
float dot(float *x, float *y, int n)
{
	float acc = 0.0;
	for (i = 0; i < n; i++) {
		acc += x[i]*y[i];
	}
	return acc;
}

int main(int argc, char *argv[])
{
	float t = 0.001f;
	float x = square_ptr(&t);
	printf("0.001    = %.10e (%a)\n"
	       "0.001^2  = %.10e (%a)\n", t, t, x, x);
	printf("0.000001 = %.10e (%a)\n", 0.000001f, 0.000001f);
	return 0;
}
