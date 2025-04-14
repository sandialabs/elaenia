#include <gmp.h>
#include <mpfr.h>

double branch_dbl(double a, double b) 
{
    double r;
    if (b >= a) {
        r = b - a + 0.5;
    } else {
        r = b / 0.5;
    }
    return r;

    /* Original with divide by zero
    double r;
    if (b >= a) {
        r = b / (b - a + 0.5);
    } else {
        r = b / 0.5;
    }
    return r;
    */

    /*  Trying just the else branch...
    double r;
    r = b / 0.5;
    return r;
    */

    /* trying just the then branch 
    double r;
    r = b / (b - a + 0.5);
    return r;
    */
}

void branch_mpfr(mpfr_t out, mpfr_t a, mpfr_t b, int prec)
{
    mpfr_t r;
    mpfr_init2(r, prec);

    if (mpfr_greaterequal_p(b, a)) {
        mpfr_sub(r, b, a, MPFR_RNDN);
        mpfr_add_d(r, r, 0.5, MPFR_RNDN);
        mpfr_div(r, b, r, MPFR_RNDN);
    } else {
        mpfr_div_d(r, b, 0.5, MPFR_RNDN);
    }
    mpfr_set(out, r, MPFR_RNDN);

    /* Trying just the else branch
    mpfr_t r;
    mpfr_init2(r, prec);
    mpfr_div_d(r, b, 0.5, MPFR_RNDN);
    mpfr_set(out, r, MPFR_RNDN);
    */

    /* Trying the then branch
    mpfr_t r;
    mpfr_init2(r, prec);
    mpfr_sub(r, b, a, MPFR_RNDN);
    mpfr_add_d(r, r, 0.5, MPFR_RNDN);
    mpfr_div(r, b, r, MPFR_RNDN);
    mpfr_set(out, r, MPFR_RNDN);
    */
}

// x = [-10; 10]
double branch_simple_dbl(double x)
{
    if (x < 6.5) {
        x = x * 3.6;
    } else {
        x = x - 8.67;
    }
    return x;
    //x = x - 8.67;
    //x = x * 3.6;
    //return x;
}

void branch_simple_mpfr(mpfr_t out, mpfr_t x, int prec)
{
    if (mpfr_cmp_d(x, 6.5) < 0) {
        mpfr_mul_d(out, x, 3.6, MPFR_RNDN);
    } else {
        mpfr_sub_d(out, x, 8.67, MPFR_RNDN);
    }
    //mpfr_sub_d(out, x, 8.67, MPFR_RNDN);
    //mpfr_mul_d(out, x, 3.6, MPFR_RNDN);
}
