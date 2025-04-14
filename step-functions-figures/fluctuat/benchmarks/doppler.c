#include "daed_builtins.h"

int main() {
    double u, v, T, out;

    u = DBETWEEN(-100, 100);
    v = DBETWEEN(20, 20000);
    T = DBETWEEN(-30, 50);
	double t1 = 331.4 + (0.6 * T);

	out = (-t1 * v) / ((t1 + u) * (t1 + u));
}
