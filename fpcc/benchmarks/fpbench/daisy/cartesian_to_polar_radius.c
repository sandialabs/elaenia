#include <math.h>

/*@
	requires 1 <= x <= 100;
	requires 1 <= y <= 100;
*/
double code(double x, double y) {
	return sqrt((x * x) + (y * y));
}