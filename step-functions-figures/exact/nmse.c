#include <stdlib.h>
#include <stdio.h>

#include <gmp.h>
#include <mpfr.h>

#include "nums.h"

double nmse_dbl(double x) {
	return ((1.0 / (x + 1.0)) - (2.0 / x)) + (1.0 / (x - 1.0));
}

void nmse_mpfr(mpfr_t out, mpfr_t x, int prec) {
	//return ((1.0 / (x + 1.0)) - (2.0 / x)) + (1.0 / (x - 1.0));
    /*
    x1 = (x + 1.0)
    x1 = 1 / x1
    x2 = 2 / x
    x1 = x1 - x2
    x2 = x - 1.0
    x2 = 1 / x2
    x1 = x1 + x2
    */

    mpfr_t x1, x2;
    mpfr_inits2(prec, x1, x2, NULL);

    mpfr_add_d(x1, x, 1.0, MPFR_RNDN);
    mpfr_d_div(x1, 1.0, x1, MPFR_RNDN);
    mpfr_d_div(x2, 2.0, x, MPFR_RNDN);
    mpfr_sub(x1, x1, x2, MPFR_RNDN);
    mpfr_sub_d(x2, x, 1.0, MPFR_RNDN);
    mpfr_d_div(x2, 1, x2, MPFR_RNDN);
    mpfr_add(out, x1, x2, MPFR_RNDN);

    mpfr_clears(x1, x2, NULL);
}

/* requires x != 1.0 && x != 2.0 && x != -1.0
 * requires -100.0 <= x <= 100.0;
 */
void test_nmse(int prec, int samples, const char* fn) {
    mpfr_t lb, ub;
    mpfr_inits2(prec, lb, ub, NULL);
    mpfr_set_ui(lb, -100, MPFR_RNDN);
    mpfr_set_ui(ub, 100, MPFR_RNDN);

    test_f(nmse_dbl, nmse_mpfr, lb, ub, prec, samples, fn);

    mpfr_clears(lb, ub, NULL);
}
