#ifndef SIN_H_INCLUDED
#define SIN_H_INCLUDED

#include <gmp.h>
#include <mpfr.h>

double sin_dbl(double x);

void sin_mpfr(mpfr_t out, mpfr_t x, int prec);

#endif
