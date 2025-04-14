#ifndef MATMUL_H_INCLUDED
#define MATMUL_H_INCLUDED

#include <gmp.h>
#include <mpfr.h>

double matmul_dbl(const double* a, const double* b, double* C);
void matmul_mpfr(mpfr_t C, mpfr_t a, mpfr_t b, int prec);

void test_matmul(int prec, int samples, const char *fn);

#endif
