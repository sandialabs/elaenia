#include "daed_builtins.h"

int main() {
    double x1, x2, x3, out;

    x1 = DBETWEEN(-15, 15);
    x2 = DBETWEEN(-15, 15);
    x3 = DBETWEEN(-15, 15);

	out = ((-(x1 * x2) - ((2.0 * x2) * x3)) - x1) - x3;
}
