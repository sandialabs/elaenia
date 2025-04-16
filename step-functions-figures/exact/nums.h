#ifndef NUMS_H_INCLUDED
#define NUMS_H_INCLUDED

#include <gmp.h>
#include <mpfr.h>

void linspace_dbl(double out[], double lb, double ub, int n);
void linspace_mpfr(mpfr_t out[], int prec, mpfr_t lb, mpfr_t ub, int n);
double rand_dbl(double a, double b);
void rand_mpfr(mpfr_t out, mpfr_t lb, mpfr_t ub, int prec, gmp_randstate_t rstate);
void sample_dbl(double out[], double lb, double ub, int n);
void sample_mpfr(mpfr_t out[], int prec, mpfr_t lb, mpfr_t ub, int n);
void get_rand_mpfr(mpfr_t out, int prec, mpfr_t lb, mpfr_t ub);

void test_f(double (*dblFun)(double), void (*mpfrFun)(mpfr_t, mpfr_t, int),
            mpfr_t lb, mpfr_t ub, int prec, int samples,
            const char* fn);

void test_f2(double (*dblFun)(double, double), 
            void (*mpfrFun)(mpfr_t, mpfr_t, mpfr_t, int),
            mpfr_t lb1, mpfr_t ub1, mpfr_t lb2, mpfr_t ub2, 
            int prec, int samples, const char* fn);

#endif
