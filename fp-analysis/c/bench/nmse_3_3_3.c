// NMSE problem 3.3.3, from
// @book{hamming-1987,
//   title = {Numerical Methods for Scientists and Engineers},
//   author = {Richard Hamming},
//   publisher = {Dover Publications},
//   year = {1987},
//   edition = {2nd},
// }

/* requires x != 1.0 && x != 2.0 && x != -1.0
 * requires -100.0 <= x <= 100.0;
 */
double ex7(double x) {
	return ((1.0 / (x + 1.0)) - (2.0 / x)) + (1.0 / (x - 1.0));
}
