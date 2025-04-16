#include <gmp.h>
#include <mpfr.h>

/* sqroot
 * (-
 *  (+ (- (+ 1 (* 1/2 x)) (* (* 1/8 x) x)) (* (* (* 1/16 x) x) x))
 *   (* (* (* (* 5/128 x) x) x) x))
 */
double sqroot_dbl(double x) {
    double y;
    y = ((((1.0 / 2.0) * x + 1) - ((1.0 / 8.0) * x * x)) + (x * x * x * (1.0 / 16.0))) - 
        ((5.0 / 128.0) * x * x * x * x);
    return y;
}

void sqroot2_mpfr(mpfr_t out, mpfr_t x, int prec) {
    mpfr_t a, b;
    mpfr_init2(a, prec);
    mpfr_init2(b, prec);

    // a = (1.0 / 2.0) * x + 1
    mpfr_set_d(a, 1.0, MPFR_RNDN);
    mpfr_div_d(a, a, 2.0, MPFR_RNDN);
    mpfr_mul(a, a, x, MPFR_RNDN);
    mpfr_add_d(a, a, 1.0, MPFR_RNDN);

    // b = (1.0 / 8.0) * x * x
    mpfr_set_d(b, 1.0, MPFR_RNDN);
    mpfr_div_d(b, b, 8.0, MPFR_RNDN);
    mpfr_mul(b, b, x, MPFR_RNDN);
    mpfr_mul(b, b, x, MPFR_RNDN);

    // a = a - b
    mpfr_sub(a, a, b, MPFR_RNDN);

    // b = (x * x * x * (1.0 / 16.0))
    mpfr_set_d(b, 1.0, MPFR_RNDN);
    mpfr_div_d(b, b, 16.0, MPFR_RNDN);
    mpfr_mul(b, b, x, MPFR_RNDN);
    mpfr_mul(b, b, x, MPFR_RNDN);
    mpfr_mul(b, b, x, MPFR_RNDN);

    // a = a + b
    mpfr_add(a, a, b, MPFR_RNDN);

    // b = (5.0 / 128.0) * x * x * x * x
    mpfr_set_d(b, 5.0, MPFR_RNDN);
    mpfr_div_d(b, b, 128.0, MPFR_RNDN);
    mpfr_mul(b, b, x, MPFR_RNDN);
    mpfr_mul(b, b, x, MPFR_RNDN);
    mpfr_mul(b, b, x, MPFR_RNDN);
    mpfr_mul(b, b, x, MPFR_RNDN);
    
    // out = a - b
    mpfr_sub(out, a, b, MPFR_RNDN);

    mpfr_clear(a);
    mpfr_clear(b);
    mpfr_free_cache();
}

