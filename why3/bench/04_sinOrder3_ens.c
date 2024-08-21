/*@ requires -2.0 <= x <= 2.0;
  @ assigns \nothing;
  @ ensures \abs(\exact(\result) - \result) < 1e-13;
 */
double sineOrder3(double x) {
	double ret = (0.954929658551372 * x) - (0.12900613773279798 * ((x * x) * x));
    return ret;
}
