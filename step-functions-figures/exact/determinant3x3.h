#ifndef DET_INCLUDED
#define DET_INCLUDED 

#include <gmp.h>
#include <mpfr.h>

double determinant_dbl(double a, double b);
void determinant_mpfr(mpfr_t out, mpfr_t a, mpfr_t b, int prec);

void test_determinant(int prec, int samples);

#endif
