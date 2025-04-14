#include <gmp.h>
#include <mpfr.h>

#include "sin.h"
/* sin
 * (-
 *  (+ (- x (/ (* (* x x) x) 6)) (/ (* (* (* (* x x) x) x) x) 120))
 *   (/ (* (* (* (* (* (* x x) x) x) x) x) x) 5040))
 *
 * -pi/2 < x < pi/2
 */
double sin_dbl(double x)
{
    double y = 
        ((x - (((x * x) * x) / 6)) + ((((((x * x) * x) * x) * x) / 120))) - 
        (((((((x * x) * x) * x) * x) * x) * x) / 5040);
    return y;
}

void sin_mpfr(mpfr_t out, mpfr_t x, int prec)
{
    mpfr_t a, b, c;
    mpfr_init2(a, prec);
    mpfr_init2(b, prec);
    mpfr_init2(c, prec);

    mpfr_pow_ui(a, x, 3, MPFR_RNDN);
    mpfr_div_ui(a, a, 6, MPFR_RNDN);
    mpfr_sub(a, x, a, MPFR_RNDN);

    mpfr_pow_ui(b, x, 5, MPFR_RNDN);
    mpfr_div_ui(b, b, 120, MPFR_RNDN);

    mpfr_add(a, a, b, MPFR_RNDN);
    
    mpfr_pow_ui(c, x, 7, MPFR_RNDN);
    mpfr_div_ui(c, c, 5040, MPFR_RNDN);

    mpfr_sub(out, a, c, MPFR_RNDN);

    mpfr_clear(a);
    mpfr_clear(b);
    mpfr_clear(c);                                 
    mpfr_free_cache();
}
