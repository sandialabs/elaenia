#include <gmp.h>
#include <mpfr.h>

/* nonlin1
 * (let ((p0 (- (+ x0 x1) x2)) (p1 (- (+ x1 x2) x0)) (p2 (- (+ x2 x0) x1)))
 *   (+ (+ p0 p1) p2))
 *
 * 0 <= z <= 999
 */
double nonlin1_dbl(double z)
{
    double a = z / (z + 1.0);
    return a;
}

void nonlin1_mpfr(mpfr_t out, mpfr_t z, int prec)
{
    mpfr_t a;
    mpfr_init2(a, prec);

    mpfr_add_d(a, z, 1.0, MPFR_RNDN);
    mpfr_div(out, z, a, MPFR_RNDN);
    mpfr_clear(a);
    mpfr_free_cache();
}
