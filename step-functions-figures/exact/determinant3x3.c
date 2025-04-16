#include <stdlib.h>
#include <stdio.h>

#include <gmp.h>
#include <mpfr.h>

#include "nums.h"

/* Determinant of the matrix [[a b c],[d e f],[g h i]]
 * Source: https://arxiv.org/pdf/2101.08733.pdf
 */
double determinant_dbl(double a, double b, double c, 
                       double d, double e, double f,
                       double g, double h, double i)
{
	return (a * e * i + b * f * g + c * d * h) -
	       (c * e * g + b * d * i + a * f * h);
}

void determinant_mpfr(mpfr_t out, 
                      mpfr_t a, mpfr_t b, mpfr_t c, 
                      mpfr_t d, mpfr_t e, mpfr_t f,
                      mpfr_t g, mpfr_t h, mpfr_t i,
                      int prec)
{
    // Intermediate values
    mpfr_t r1, r2, r3;
    mpfr_init2(r1, prec);
    mpfr_init2(r2, prec);
    mpfr_init2(r3, prec);

    // r1 = a * e * i
    mpfr_mul(r1, a, e, MPFR_RNDN);
    mpfr_mul(r1, r1, i, MPFR_RNDN);

    // r2 = b * f * g
    mpfr_mul(r2, b, f, MPFR_RNDN);
    mpfr_mul(r2, r2, g, MPFR_RNDN);

    // r3 = c * d * h
    mpfr_mul(r3, c, d, MPFR_RNDN);
    mpfr_mul(r3, r3, h, MPFR_RNDN);

    // out = a * e * i + b * f * g + c * d * h
    mpfr_add(out, r1, r2, MPFR_RNDN);
    mpfr_add(out, out, r3, MPFR_RNDN);

    // r1 = c * e * g
    mpfr_mul(r1, c, e, MPFR_RNDN);
    mpfr_mul(r1, r1, g, MPFR_RNDN);

    // r2 = b * d * i
    mpfr_mul(r2, b, d, MPFR_RNDN);
    mpfr_mul(r2, r2, i, MPFR_RNDN);

    // r3 = a * f * h
    mpfr_mul(r3, a, f, MPFR_RNDN);
    mpfr_mul(r3, r3, h, MPFR_RNDN);

    // r1 = c * e * g + b * d * i + a * f * h
    mpfr_add(r1, r1, r2, MPFR_RNDN);
    mpfr_add(r1, r1, r3, MPFR_RNDN);

    // out = (a * e * i + b * f * g + c * d * h) -
    //       (c * e * g + b * d * i + a * f * h);
    mpfr_sub(out, out, r1, MPFR_RNDN);
}

void test_determinant(int prec, int samples)
{

    int params = 9;

    mpfr_t lba, uba, lbb, ubb, lbc, ubc;
    mpfr_t lbd, ubd, lbe, ube, lbf, ubf;
    mpfr_t lbg, ubg, lbh, ubh, lbi, ubi;

    mpfr_inits2(prec, lba, uba, lbb, ubb, lbc, ubc,
                      lbd, ubd, lbe, ube, lbf, ubf,
                      lbg, ubg, lbh, ubh, lbi, ubi, NULL);

    // mpfr_t bounds[params * 2]
    mpfr_t* bounds[9 * 2] = 
        { &lba, &uba, &lbb, &ubb, &lbc, &ubc, 
          &lbd, &ubd, &lbe, &ube, &lbf, &ubf,
          &lbg, &ubg, &lbh, &ubh, &lbi, &ubi };

    for (int i = 0; i < params * 2; i++) 
    {
        mpfr_set_si(*bounds[i], i % 2 == 0 ? -10 : 10, MPFR_RNDN);
    }

    // 9 params...
    
    FILE* f = fopen("determinant-exp.csv", "w");
    fprintf(f, "a_dbl,b_dbl,c_dbl,d_dbl,e_dbl,f_dbl,g_dbl,h_dbl,i_dbl,dbl_out,");
    fprintf(f, "a_mpfr,b_mpfr,c_mpfr,d_mpfr,e_mpfr,f_mpfr,g_mpfr,h_mpfr,i_mpfr,mpfr_out,");
    fprintf(f, "err\n");

    if (f == NULL)
    {
        printf("Error opening data.csv");
        exit(1);
    }

    // double inputs.  Will be initialized by rounded MPFR samples
    double dbl_outs;
    double dbl_ins_vals[params][samples];

    // Initialize temp vars
    mpfr_t sub;
    mpfr_init2 (sub, prec);

    // Set up MPFR outputs
    mpfr_t mpfr_out;
    mpfr_init2(mpfr_out, prec);

    mpfr_t mpfr_ins_vals[params][samples];

    // initialize inputs
    printf("initializing inputs...\n");
    for (int i = 0; i < params; i++) {
        for (int j = 0; j < samples; j++) {
            mpfr_init2(mpfr_ins_vals[i][j], prec);
        }

        sample_mpfr(mpfr_ins_vals[i], prec, *bounds[i * 2], *bounds[i * 2 + 1], samples);

        for (int j = 0; j < samples; j++) {
            dbl_ins_vals[i][j] = mpfr_get_d(mpfr_ins_vals[i][j], MPFR_RNDN);
        }
    }

    // Compare
    long curr = 0;
    long count = samples * samples * samples *
                 samples * samples * samples *
                 samples * samples * samples;

    int is[9];
     
    printf("comparing (N = %ld)...\n", count);
    for (is[0] = 0; is[0] < samples; is[0]++) {
    for (is[1] = 0; is[1] < samples; is[1]++) {
    for (is[2] = 0; is[2] < samples; is[2]++) {
    for (is[3] = 0; is[3] < samples; is[3]++) {
    for (is[4] = 0; is[4] < samples; is[4]++) {
    for (is[5] = 0; is[5] < samples; is[5]++) {
    for (is[6] = 0; is[6] < samples; is[6]++) {
    for (is[7] = 0; is[7] < samples; is[7]++) {
    for (is[8] = 0; is[8] < samples; is[8]++) {
        printf("sample %ld/%ld = (%.1f %% complete)\r", curr, count, 
               100. * ((double) curr) / ((double) count));
        curr++;

        // Compute error
        dbl_outs = 
            determinant_dbl(dbl_ins_vals[0][is[0]],
                            dbl_ins_vals[1][is[1]],
                            dbl_ins_vals[2][is[2]],
                            dbl_ins_vals[3][is[3]],
                            dbl_ins_vals[4][is[4]],
                            dbl_ins_vals[5][is[5]],
                            dbl_ins_vals[6][is[6]],
                            dbl_ins_vals[7][is[7]],
                            dbl_ins_vals[8][is[8]]);
        
        determinant_mpfr(mpfr_out,
                         mpfr_ins_vals[0][is[0]],
                         mpfr_ins_vals[1][is[1]],
                         mpfr_ins_vals[2][is[2]],
                         mpfr_ins_vals[3][is[3]],
                         mpfr_ins_vals[4][is[4]],
                         mpfr_ins_vals[5][is[5]],
                         mpfr_ins_vals[6][is[6]],
                         mpfr_ins_vals[7][is[7]],
                         mpfr_ins_vals[8][is[8]], prec);

        mpfr_sub_d(sub, mpfr_out, dbl_outs, MPFR_RNDN);
        mpfr_abs(sub, sub, MPFR_RNDN);

        // Write to csv
        for (int i = 0; i < params; i++) { 
            fprintf(f, "%f,", dbl_ins_vals[i][is[i]]);
        }
        fprintf(f, "%f,", dbl_outs);

        for (int i = 0; i < params; i++) {
            mpfr_out_str(f, 10, 0, mpfr_ins_vals[i][is[i]], MPFR_RNDN);
            fprintf(f, ",");
        }
        mpfr_out_str(f, 10, 0, mpfr_out, MPFR_RNDN);
        fprintf(f, ",");
        mpfr_out_str(f, 10, 0, sub, MPFR_RNDN);
        fprintf(f, "\n");
    }}}}}}}}}
    printf("\nsample %ld/%ld (100%% complete)\n", count, count);

    // freeing memory
    printf("\n freeing memory...\n");
    for (int i = 0; i < params; i++) {
        for (int j = 0; j < samples; j++) {
            mpfr_clear(mpfr_ins_vals[i][j]);
        }
    }
    mpfr_clears(sub, mpfr_out, NULL);
    mpfr_clears(lba, uba, lbb, ubb, lbc, ubc,
                lbd, ubd, lbe, ube, lbf, ubf,
                lbg, ubg, lbh, ubh, lbi, ubi, NULL);
}

