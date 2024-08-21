/*@ requires -1.0 <= x <= 1.0;
  @ assigns \nothing;
  @ ensures -1.0 <= \result <= 1.0;
  // Note: you may need to make this -1.0-e <= \result <= 1.0+e;
  // for some small e when using -wp-model +float

  // The below statement is not provable with AR because it relies on the fact
  // that a the given 3rd-order taylor series does in fact approximate sine

  // @ ensures \abs(\result - \sin(x)) <= 1e-3;
 */
double sineOrder3(double x) {
	double ret = (0.954929658551372 * x) - (0.12900613773279798 * ((x * x) * x));
    return ret;
}

