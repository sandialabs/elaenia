#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include <gmp.h>
#include <mpfr.h>

#include "sin.h"
#include "nonlin1.h"
#include "sqroot.h"
#include "branch.h"
#include "nums.h"
#include "determinant3x3.h"
#include "matmul.h"
#include "nmse.h"
#include "rosa.h"

#ifndef N
#define N 1024
#endif

const int PREC = 200; // Large enough to be treated as exact
//const int SAMPLES = 598948;
//const long SAMPLES = 100000;
const long SAMPLES = N;
const long SAMPLES_SMALL = 4;

/* Outputting data
 * --------------------------------------------------------------------------- */
void print_errs(double dbl_ins[], double dbl_outs[], 
                mpfr_t mpfr_ins[], mpfr_t mpfr_outs[], 
                mpfr_t errs[]) 
{
    for (int i = 0; i < SAMPLES; i++)
    {
        printf("sin(%f) = %f\n", dbl_ins[i], dbl_outs[i]);

        printf("sin(");
        mpfr_out_str(stdout, 10, 0, mpfr_ins[i], MPFR_RNDN);
        printf(") = ");
        mpfr_out_str(stdout, 10, 0, mpfr_outs[i], MPFR_RNDN);
        printf("\nerror = ");
        mpfr_out_str(stdout, 10, 0, errs[i], MPFR_RNDN);
        printf("\n\n");
    }
}

/* Runners
 * --------------------------------------------------------------------------- */
void test_sin()
{
    mpfr_t mpfr_lb, mpfr_ub;
    mpfr_init2 (mpfr_lb, PREC);
    mpfr_init2 (mpfr_ub, PREC);

    // Set up MPFR inputs
    mpfr_const_pi(mpfr_lb, MPFR_RNDN);
    mpfr_mul_d(mpfr_lb, mpfr_lb, 0.0, MPFR_RNDN);     // -2pi

    mpfr_const_pi(mpfr_ub, MPFR_RNDN);
    mpfr_mul_d(mpfr_ub, mpfr_ub, 0.5, MPFR_RNDN);     // 2pi

    test_f(sin_dbl, sin_mpfr, mpfr_lb, mpfr_ub, PREC, SAMPLES, "sin-exp.csv");

    mpfr_clear(mpfr_lb);
    mpfr_clear(mpfr_ub);
}

void test_nonlin1()
{
    mpfr_t mpfr_lb, mpfr_ub;
    mpfr_init2 (mpfr_lb, PREC);
    mpfr_init2 (mpfr_ub, PREC);
    mpfr_set_ui(mpfr_lb, 0, MPFR_RNDN);
    mpfr_set_ui(mpfr_ub, 999, MPFR_RNDN);

    test_f(nonlin1_dbl, nonlin1_mpfr, mpfr_lb, mpfr_ub, PREC, SAMPLES, "nonlin1-exp.csv");

    mpfr_clear(mpfr_lb);
    mpfr_clear(mpfr_ub);
}

void test_sqrt()
{
    mpfr_t mpfr_lb, mpfr_ub;
    mpfr_init2(mpfr_lb, PREC);
    mpfr_init2(mpfr_ub, PREC);
    mpfr_set_ui(mpfr_lb, 0, MPFR_RNDN);
    mpfr_set_ui(mpfr_ub, 999, MPFR_RNDN);

    test_f(sqroot_dbl, sqroot_mpfr, mpfr_lb, mpfr_ub, PREC, SAMPLES, "sqrt-exp.csv");

    mpfr_clear(mpfr_lb);
    mpfr_clear(mpfr_ub);
}

void test_branch()
{
    mpfr_t lb1, ub1, lb2, ub2;
    mpfr_init2(lb1, PREC);
    mpfr_init2(ub1, PREC);
    mpfr_init2(lb2, PREC);
    mpfr_init2(ub2, PREC);
    mpfr_set_ui(lb1, 0, MPFR_RNDN);
    mpfr_set_ui(ub1, 100, MPFR_RNDN);
    mpfr_set_ui(lb2, 0, MPFR_RNDN);
    mpfr_set_ui(ub2, 100, MPFR_RNDN);

    test_f2(branch_dbl, branch_mpfr, lb1, ub1, lb2, ub2, PREC, SAMPLES, "branch-exp.csv");

    mpfr_clear(lb1);
    mpfr_clear(ub1);
    mpfr_clear(lb2);
    mpfr_clear(ub2);
}

void test_branch_simple()
{
    mpfr_t lb, ub;
    mpfr_init2(lb, PREC);
    mpfr_init2(ub, PREC);
    mpfr_set_si(lb, -10, MPFR_RNDN);
    mpfr_set_si(ub, 10, MPFR_RNDN);

    test_f(branch_simple_dbl, branch_simple_mpfr, lb, ub, PREC, SAMPLES, "branch-simple-exp.csv");

    mpfr_clear(lb);
    mpfr_clear(ub);
}

int main (void)
{
    srand(42);
    printf("Running with N = %ld\n", SAMPLES);
    printf("test_nonlin1\n");       test_nonlin1();
    printf("test_sin\n");           test_sin();
    printf("test_sqrt\n");          test_sqrt();
    printf("test_branch\n");        test_branch();
    printf("test_branch_simple\n"); test_branch_simple();
    printf("test_determinant\n");   test_determinant(PREC, SAMPLES_SMALL);
    printf("test_matmul\n");        test_matmul(PREC, SAMPLES, "matmul-exp.csv");
    printf("test_nmse\n");          test_nmse(PREC, SAMPLES, "nmse-exp.csv");
    test_rosa(PREC, SAMPLES);
    fflush(stdout);
}
