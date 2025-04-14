/* Reciprocal square root.
 * Source: Samuel D. Pollard. When Does a Bit Matter? Techniques for Verifying the Correctness of Assembly Languages and Floating-Point Programs. PhD Thesis, University of Oregon, Eugene, USA, Jun 2021. 
 * Computes 1/sqrt(x)
 * Requires x > 0
 * Performs 5 iterations. This should be _very_ close to the exact solution.
 */

double rsqrt(double x)
{
	int i;
	double xhalf = x * 0.5f;
	double y = 0.5 / x; // Initial guess
	for (i = 0; i < 5; i++) {
		y = y * (1.5 - (xhalf * y * y));
	}
	return y;
}

