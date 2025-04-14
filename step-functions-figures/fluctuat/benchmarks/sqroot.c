#include "daed_builtins.h"

int main() {
    double x, out;

    x = DBETWEEN(0, 1);

    out = (0.954929658551372 * x) - (0.12900613773279798 * ((x * x) * x));
}
