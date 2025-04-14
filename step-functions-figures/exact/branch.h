#ifndef BRANCH_H_INCLUDED
#define BRANCH_H_INCLUDED

#include <gmp.h>
#include <mpfr.h>

double branch_dbl(double a, double b);
void branch_mpfr(mpfr_t out, mpfr_t a, mpfr_t b, int prec);

double branch_simple_dbl(double x);
void branch_simple_mpfr(mpfr_t out, mpfr_t x, int prec);

#endif
