/* Determinant of the matrix [[a b c],[d e f],[g h i]]
 * Source: https://arxiv.org/pdf/2101.08733.pdf
 */
double determinant_dbl(double a, double b, double c, 
                       double d, double e, double f,
                       double g, double h, double i)
{
	return (a * e * i + b * f * g + c * d * h) -
	       (c * e * g + b * d * i + a * f * h);
}

