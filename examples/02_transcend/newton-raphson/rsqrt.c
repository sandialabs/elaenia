/*
Computes Newton-Raphson Iteration
  x_{n+1} = x_n - f(x_n) / f'(x_n)
Further reading: https://inria.hal.science/inria-00071899/document
*/

#include <stdio.h>

#define MAX_ITERS 10
#define TOL 1e-6

double rsqrt(double a)
{
	double xn1, xn;
	int n = 0;
	// Initial guess
	xn = 1./a;
	do {
		if (n > MAX_ITERS) {
			break;
		}
		xn1 = xn;
		xn = 0.5 * xn * (3 - a * xn * xn);
		n++;
	} while ((((xn - xn1) * (xn - xn1)) > TOL));
	return xn;

}

int main()
{
	double r = rsqrt(99.0); // 0.1005037815
	printf("1/sqrt = %.8f\n", r);
	nri(1.0);
}
