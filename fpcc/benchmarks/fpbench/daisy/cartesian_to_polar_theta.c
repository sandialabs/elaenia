
/*@
	requires 1 <= x <= 100;
	requires 1 <= y <= 100;
*/
double code(double x, double y) {
	return atan((y / x)) * (180.0 / 3.14159265359);
}