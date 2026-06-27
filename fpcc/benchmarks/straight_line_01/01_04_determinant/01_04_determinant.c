/*@
  requires 0.0 <= a <= 1000;
  requires 0.0 <= b <= 1000;
  requires 0.0 <= c <= 1000;
  requires 0.0 <= d <= 1000;
  requires 0.0 <= e <= 1000;
  requires 0.0 <= f <= 1000;
  requires 0.0 <= g <= 1000;
  requires 0.0 <= h <= 1000;
  requires 0.0 <= i <= 1000;
*/
double determinant_dbl(double a, double b, double c, 
                       double d, double e, double f,
                       double g, double h, double i)
{
	return (a * e * i + b * f * g + c * d * h) -
	       (c * e * g + b * d * i + a * f * h);
}

