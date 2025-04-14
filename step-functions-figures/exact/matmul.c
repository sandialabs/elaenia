#include <stdio.h>
#include <stdlib.h>

#include <gmp.h>
#include <mpfr.h>

#include "nums.h"

void matmul_dbl(const double* a, const double* b, double* C)
{
    C[0] = a[0]*b[0] + a[1]*b[3] + a[2]*b[6];
    C[1] = a[0]*b[1] + a[1]*b[4] + a[2]*b[7];
    C[2] = a[0]*b[2] + a[1]*b[5] + a[2]*b[8];

    C[3] = a[3]*b[0] + a[4]*b[3] + a[5]*b[6];
    C[4] = a[3]*b[1] + a[4]*b[4] + a[5]*b[7];
    C[5] = a[3]*b[2] + a[4]*b[5] + a[5]*b[8];

    C[6] = a[6]*b[0] + a[7]*b[3] + a[8]*b[6];
    C[7] = a[6]*b[1] + a[7]*b[4] + a[8]*b[7];
    C[8] = a[6]*b[2] + a[7]*b[5] + a[8]*b[8];
}

void matmul_mpfr_cell(mpfr_t* C, int cell, mpfr_t* a, mpfr_t* b,
                      mpfr_t x1, mpfr_t x2, int prec)
{
    int a1 = cell / 3 * 3;
    int a2 = a1 + 1;
    int a3 = a2 + 1;

    int b1 = cell % 3;
    int b2 = b1 + 3;
    int b3 = b2 + 3;

    /*
    printf("c[%d] = a[%d] * b[%d] + a[%d] * b[%d] + a[%d] * b[%d]\n",
           cell, a1, b1, a2, b2, a3, b3);
    */

    mpfr_mul(x1, a[a1], b[b1], MPFR_RNDN);
    mpfr_mul(x2, a[a2], b[b2], MPFR_RNDN);
    mpfr_add(x1, x1, x2, MPFR_RNDN);
    mpfr_mul(x2, a[a3], b[b3], MPFR_RNDN);
    mpfr_add(C[cell], x1, x2, MPFR_RNDN);

}

void matmul_mpfr(mpfr_t* C, mpfr_t* a, mpfr_t* b, int prec)
{
    mpfr_t x1, x2;
    mpfr_init2(x1, prec);
    mpfr_init2(x2, prec);

    for (int i = 0; i < 9; i++) {
        matmul_mpfr_cell(C, i, a, b, x1, x2, prec);
    }
    //exit(1);

    mpfr_clears(x1, x2, NULL);
}

void test_matmul(int prec, int samples, const char *fn) {
    // two 3x3 matrices = 18 effective params
    int params = 18;

    // Initialize bounds
    mpfr_t lba, uba, lbb, ubb;
    mpfr_inits2(prec, lba, uba, lbb, ubb, NULL);

    mpfr_set_si(lba, -1000, MPFR_RNDN);
    mpfr_set_si(uba,  1000, MPFR_RNDN);
    mpfr_set_si(lbb, -1000, MPFR_RNDN);
    mpfr_set_si(ubb,  1000, MPFR_RNDN);

    // Open output file
    FILE * f = fopen(fn, "w");
    if (f == NULL)
    {
        printf("Error opening %s\n", fn);
        exit(1);
    }

    // Headers
    for (int i = 0; i < 9; i ++)
    {
        fprintf(f, "a[%d]_dbl,", i);
        fprintf(f, "b[%d]_dbl,", i);
    }

    for (int i = 0; i < 9; i ++)
    {
        fprintf(f, "C[%d]_dbl,", i);
    }

    for (int i = 0; i < 9; i ++)
    {
        fprintf(f, "a[%d]_mpfr,", i);
        fprintf(f, "b[%d]_mpfr,", i);
    }
    for (int i = 0; i < 9; i ++)
    {
        fprintf(f, "C[%d]_mpfr,", i);
    }

    for (int i = 0; i < 9; i++) {
        fprintf(f, "C[%d]_err", i);
        if (i < 8) fprintf(f, ",");
    }
    fprintf(f, "\n");

    // Compare
    int curr = 0;
    /*
    long count = samples * samples * samples * samples * samples * samples *
                 samples * samples * samples * samples * samples * samples *
                 samples * samples * samples * samples * samples * samples;
    */

    // Things we need for the big loop
    double a_dbl[9];
    double b_dbl[9];
    double c_dbl[9];
    mpfr_t a_mpfr[9];
    mpfr_t b_mpfr[9];
    mpfr_t c_mpfr[9];

    mpfr_t sub[9];
    for (int i = 0; i < 9; i++) {
        mpfr_inits2(prec, sub[i], a_mpfr[i], b_mpfr[i], c_mpfr[i], NULL);
    }

    // initialize random state
    gmp_randstate_t rstate;
    gmp_randinit_mt(rstate);
    unsigned long seed;
    gmp_randseed_ui(rstate, seed);

    for (long i = 0; i < samples; i++)
    {
        if (i % 1000 == 0) {
            printf("sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
            //fflush(stdout);
        }
        curr++;

        // build the input arrays
        for (int i = 0; i < 9; i++)
        {
            rand_mpfr(a_mpfr[i], lba, uba, prec, rstate);
            rand_mpfr(b_mpfr[i], lba, uba, prec, rstate);

            a_dbl[i] = mpfr_get_d(a_mpfr[i], MPFR_RNDN);
            b_dbl[i] = mpfr_get_d(b_mpfr[i], MPFR_RNDN);
        }

        // perform the matmul
        matmul_dbl(a_dbl, b_dbl, c_dbl);
        matmul_mpfr(c_mpfr, a_mpfr, b_mpfr, prec);

        // compute the error
        for (int i = 0; i < 9; i++) {
            mpfr_sub_d(sub[i], c_mpfr[i], c_dbl[i], MPFR_RNDN);
            mpfr_abs(sub[i], sub[i], MPFR_RNDN);
        }

        // write to the csv
        for (int i = 0; i < 9; i++) {
            fprintf(f, "%f,", a_dbl[i]);
            fprintf(f, "%f,", b_dbl[i]);
        }

        for (int i = 0; i < 9; i++) {
            fprintf(f, "%f,", c_dbl[i]);
        }

        for (int i = 0; i < 9; i++) {
            mpfr_out_str(f, 10, 0, a_mpfr[i], MPFR_RNDN);
            fprintf(f, ",");
            mpfr_out_str(f, 10, 0, b_mpfr[i], MPFR_RNDN);
            fprintf(f, ",");
        }

        for (int i = 0; i < 9; i ++) {
            mpfr_out_str(f, 10, 0, c_mpfr[i], MPFR_RNDN);
            fprintf(f, ",");
        }

        for (int i = 0; i < 9; i++) {
            mpfr_out_str(f, 10, 0, sub[i], MPFR_RNDN);
            fprintf(f, ",");
        }
        fprintf(f,"\n");
    }
    fflush(stdout);
    printf("\nsample %d/%d (100%% complete)\n", samples, samples);
}
