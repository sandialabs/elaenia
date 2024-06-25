/*@ requires -2.0 <= x <= 2.0;
  @ ensures -1.0 <= \result <= 1.0;
  // Note: you may need to make this -1.0-x <= \result <= 1.0+x; for some small x
 */
double sineOrder3(double x) {
	double ret = (0.954929658551372 * x) - (0.12900613773279798 * ((x * x) * x));
    return ret;
}

