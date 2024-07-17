/* Frama-C Examples (at the UUR level) which gives some examples
 * of where Frama-C may have trouble parsing and analyzing, their
 * build instructions, and the solutions.
 */

#include "sqrt.h"

double sqrt_in_const(double a, double b)
{
	static const double x2 = x*x;
	static const double y2 = y*y;
	static const double c = sqrt(x2*(1-y2));
	static const double c2 = c*c;
	return a + b + c2;
}

int main(int argc, char *argv[])
{
	sqrt_in_const(1.0, 1.0);
	return 0;
}
