#include <gmp.h>
#include <mpfr.h>

double branch_simple_dbl(double x)
{
    if (x < 6.5) {
        x = x * 3.6;
    } else {
        x = x - 8;
    }
    return x;
}

void branch_simple_mpfr
