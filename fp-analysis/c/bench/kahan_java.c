/* From https://people.eecs.berkeley.edu/~wkahan/JAVAhurt.pdf
 * p. 38
 * G(y, z) := 108 – ( 815 – 1500/z )/y
 * The series x_n = G(x_n, x_{n-1}), x_n converges to 5,
 * but pretty much any limited-precision solution converges to 100
 */
#include <stdio.h>

#define N 10

/* Initial values x0 = 4.0, x1 = 4.25 */
double muller(double x0, double x1)
{
    double xn1 = x0;
    double xn  = x1;
	double tmp;
	for (int i = 0; i < N; i++) {
		tmp = xn;
		xn  = 108. - (815. - 1500./xn1) / xn;
		xn1 = tmp;
	}
	return xn;
}

int main(void)
{
	printf("muller(4.0, 4.25) (n = %d) = %.15f\n", N, muller(4.0, 4.25));
}
