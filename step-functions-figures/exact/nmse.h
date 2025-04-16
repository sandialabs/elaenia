#ifndef NMSE_H_INCLUDED
#define NMSE_H_INCLUDED

#include <gmp.h>
#include <mpfr.h>

double nmse_dbl(double x);
void nmse_mpfr(mpfr_t out, mpfr_t x, int prec);

void test_nmse(int prec, int samples, const char* fn);

#endif
