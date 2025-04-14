#include "daed_builtins.h"

int main() {
    double x, out;

    x = DBETWEEN(-1.57079632679, 1.57079632679);

	out = (((1.0 + (0.5 * x)) - ((0.125 * x) * x)) + (((0.0625 * x) * x) * x)) - ((((0.0390625 * x) * x) * x) * x);
}
