#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>

#include <gmp.h>
#include <mpfr.h>

    // Set up MPFR inputs
mpfr_t mpfr_outs[1000000];
mpfr_t mpfr_ins[1000000];
mpfr_t errors[1000000];

/* Numerical helpers for sampling */

/* Linspace functions for getting samples
 * --------------------------------------------------------------------------- */
// Get n evenly spaced values between lb and ub
void linspace_dbl(double out[], double lb, double ub, int n) {
    double step = (ub - lb) / n;
    for (int i = 0; i < n; i++)
    {
        out[i] = lb + i * step;
    }
}

// Get n evenly spaced values between lb and ub, put into out
void linspace_mpfr(mpfr_t out[], int prec, mpfr_t lb, mpfr_t ub, int n) {
    mpfr_t a, b, step;
    mpfr_init2(a, prec);
    mpfr_init2(b, prec);
    mpfr_init2(step, prec);

    mpfr_sub(a, ub, lb, MPFR_RNDN);
    mpfr_div_ui(step, a, n, MPFR_RNDN);

    for (int i = 0; i < n; i++)
    {
        mpfr_init2(out[i], prec);

        mpfr_mul_ui(a, step, i, MPFR_RNDN);
        mpfr_add(out[i], lb, a, MPFR_RNDN);
    }
}

/* Generating random numbers is difficult, so we use the R versions
 * https://github.com/SurajGupta/r-source/blob/a28e609e72ed7c47f6ddfbb86c85279a0750f0b7/src/nmath/standalone/sunif.c
 * --------------------------------------------------------------------------- */

static unsigned int I1 = 1234, I2 = 5678;

void set_seed() {
    I1 = rand() * (1000);
    I2 = rand() * (1000);
}

double unif_rand()
{
    // Need to set the seed I1 and I2
    I1= 36969*(I1 & 0177777) + (I1>>16);
    I2= 18000*(I2 & 0177777) + (I2>>16);
    return ((I1 << 16)^(I2 & 0177777)) * 2.328306437080797e-10; /* in [0,1) */
}

// https://github.com/SurajGupta/r-source/blob/master/src/nmath/runif.c
double rand_dbl(double a, double b)
{
    set_seed();
    if (a == b) {
        return a;
    }
    else {
        return a + (b - a) * unif_rand();
    }
}

void rand_mpfr(mpfr_t out, mpfr_t lb, mpfr_t ub, int prec, gmp_randstate_t rstate) {
    mpfr_t u;
    mpfr_init2(u, prec);

    // initialize the random number generator
    mpfr_urandomb(out, rstate);
    mpfr_sub(u, ub, lb, MPFR_RNDN);
    mpfr_mul(out, out, u, MPFR_RNDN);
    mpfr_add(out, out, lb, MPFR_RNDN);
}

/* Linspace isn't always the best option for sampling
 * --------------------------------------------------------------------------- */
// Get n samples randomly from the range
void sample_dbl(double out[], double lb, double ub, int n) {
    for (int i = 0; i < n; i++) {
        out[i] = rand_dbl(lb, ub);
    }
}

void sample_mpfr(mpfr_t out[], int prec, mpfr_t lb, mpfr_t ub, int n) {
    gmp_randstate_t rstate;
    gmp_randinit_mt(rstate);
    unsigned long seed;
    gmp_randseed_ui(rstate, seed);
    for (int i = 0; i < n; i++) {
        mpfr_init2(out[i], prec);
        rand_mpfr(out[i], lb, ub, prec, rstate);
    }
}

void get_rand_mpfr(mpfr_t out, int prec, mpfr_t lb, mpfr_t ub) {
    gmp_randstate_t rstate;
    gmp_randinit_mt(rstate);
    unsigned long seed;
    gmp_randseed_ui(rstate, seed);
    rand_mpfr(out, lb, ub, prec, rstate);
}

void write_csv(double dbl_ins[], double dbl_outs[], 
               mpfr_t mpfr_ins[], mpfr_t mpfr_outs[], 
               mpfr_t errs[], const char *fn, int samples) {
    FILE* f = fopen(fn, "w");

    if (f == NULL)
    {
        printf("Error opening %s\n", fn);
        exit(1);
    }

    fprintf(f, "dbl_in,dbl_out,mpfr_in,mpfr_out,err\n");

    for (int i = 0; i < samples; i++)
    {
        fprintf(f, "%f,%f,", dbl_ins[i], dbl_outs[i]);
        mpfr_out_str(f, 10, 0, mpfr_ins[i], MPFR_RNDN);
        fprintf(f, ",");
        mpfr_out_str(f, 10, 0, mpfr_outs[i], MPFR_RNDN);
        fprintf(f, ",");
        mpfr_out_str(f, 10, 0, errs[i], MPFR_RNDN);
        fprintf(f, "\n");
    }
}


// 2 parameter functions
void write_csv2(double dbl_ins1[], double dbl_ins2[], double dbl_outs[],
                mpfr_t mpfr_ins1[], mpfr_t mpfr_ins2[], mpfr_t mpfr_outs[],
                mpfr_t errs[], const char *fn, int samples)
{
    FILE* f = fopen(fn, "w");

    if (f == NULL)
    {
        printf("Error opening %s\n", fn);
        exit(1);
    }

    fprintf(f, "dbl_in1,dbl_in2,dbl_out,mpfr_in1,mpfr_in2,mpfr_out,err\n");

    for (int i = 0; i < samples; i++)
    {
        fprintf(f, "%f,%f,%f,", dbl_ins1[i], dbl_ins2[i], dbl_outs[i]);
        mpfr_out_str(f, 10, 0, mpfr_ins1[i], MPFR_RNDN);
        fprintf(f, ",");
        mpfr_out_str(f, 10, 0, mpfr_ins2[i], MPFR_RNDN);
        fprintf(f, ",");
        mpfr_out_str(f, 10, 0, mpfr_outs[i], MPFR_RNDN);
        fprintf(f, ",");
        mpfr_out_str(f, 10, 0, errs[i], MPFR_RNDN);
        fprintf(f, "\n");
    }
}

void test_f(double (*dblFun)(double), void (*mpfrFun)(mpfr_t, mpfr_t, int),
            mpfr_t lb, mpfr_t ub, int prec, int samples, const char *fn)
{
    // set up double inputs
    double dbl_outs[samples];
    double dbl_ins[samples];

    // Initialize the vars
    mpfr_t sub;
    mpfr_init2 (sub, prec);

    // initialize vars
    for (int i = 0; i < samples; i++) {
        mpfr_init2(mpfr_outs[i], prec);
        mpfr_init2(mpfr_ins[i], prec);
        mpfr_init2(errors[i], prec);
    }

    /* Assuming branch stability */
    sample_mpfr(mpfr_ins, prec, lb, ub, samples);

    /* Branch instability case */
    sample_mpfr(mpfr_ins, prec, lb, ub, samples - 1);
    mpfr_set_str(mpfr_ins[samples - 1], "6.4999999999999999999999999999999", 10, MPFR_RNDN);

    for (int i = 0; i < samples; i++) {
        dbl_ins[i] = mpfr_get_d(mpfr_ins[i], MPFR_RNDN);
    }

    // Compute the error
    for (int i = 0; i < samples; i++) 
    {
        dbl_outs[i] = dblFun(dbl_ins[i]);
        mpfrFun(mpfr_outs[i], mpfr_ins[i], prec);         
        mpfr_sub_d(sub, mpfr_outs[i], dbl_outs[i], MPFR_RNDN);
        mpfr_abs(errors[i], sub, MPFR_RNDN);
    }

    // output
    write_csv(dbl_ins, dbl_outs, mpfr_ins, mpfr_outs, errors, fn, samples);
    //print_errs(dbl_ins, dbl_outs, mpfr_ins, mpfr_outs, errors);
}

// We write to the csv in place to avoid memory concerns
void test_f2(double (*dblFun)(double, double), 
            void (*mpfrFun)(mpfr_t, mpfr_t, mpfr_t, int),
            mpfr_t lb1, mpfr_t ub1, mpfr_t lb2, mpfr_t ub2,
            int prec, int samples, const char * fn)
{
    // Open csv file
    FILE* f = fopen(fn, "w");

    if (f == NULL)
    {
        printf("Error opening %s\n", fn);
        exit(1);
    }
    fprintf(f, "dbl_in1,dbl_in2,dbl_out,mpfr_in1,mpfr_in2,mpfr_out,err\n");

    // double inputs
    int sq_sample = (int) sqrt((double) samples);
    double dbl_outs;
    double dbl_ins1[sq_sample];
    double dbl_ins2[sq_sample];
    // dbl_ins will be rounded from MPFR samples

    // Initialize temp vars
    mpfr_t sub;
    mpfr_init2 (sub, prec);

    // Set up MPFR outputs
    mpfr_t mpfr_out;
    mpfr_init2(mpfr_out, prec);

    mpfr_t mpfr_ins1[sq_sample];
    mpfr_t mpfr_ins2[sq_sample];

    // initialize inputs
    for (int i = 0; i < sq_sample; i++) {
        mpfr_init2(mpfr_ins1[i], prec);
        mpfr_init2(mpfr_ins2[i], prec);
    }
    sample_mpfr(mpfr_ins1, prec, lb1, ub1, sq_sample); 
    sample_mpfr(mpfr_ins2, prec, lb2, ub2, sq_sample); 

    // initialize double samples
    for (int i = 0; i < sq_sample; i++) {
        dbl_ins1[i] = mpfr_get_d(mpfr_ins1[i], MPFR_RNDN);
        dbl_ins2[i] = mpfr_get_d(mpfr_ins2[i], MPFR_RNDN);
    }

    printf("  All initialized, sq_sample = %d\n", sq_sample);
    // Write to csv file
    long count = sq_sample * sq_sample;
    for (int i = 0; i < sq_sample; i++) 
    {
        for (int j = 0; j < sq_sample; j++)
        {
            if (j == 0) {
                printf("sample %d/%ld (%.1f%% complete)\r", i * sq_sample + j, count, 100. * ((double) (i * sq_sample + j)) / ((double) count));
            }
            // Compute error
            dbl_outs = dblFun(dbl_ins1[i], dbl_ins2[j]);
            mpfrFun(mpfr_out, mpfr_ins1[i], mpfr_ins2[j], prec);         
            mpfr_sub_d(sub, mpfr_out, dbl_outs, MPFR_RNDN);
            mpfr_abs(sub, sub, MPFR_RNDN);

            // Write to csv
            fprintf(f, "%f,%f,%f,", dbl_ins1[i], dbl_ins2[i], dbl_outs);
            mpfr_out_str(f, 10, 0, mpfr_ins1[i], MPFR_RNDN);
            fprintf(f, ",");
            mpfr_out_str(f, 10, 0, mpfr_ins2[i], MPFR_RNDN);
            fprintf(f, ",");
            mpfr_out_str(f, 10, 0, mpfr_out, MPFR_RNDN);
            fprintf(f, ",");
            mpfr_out_str(f, 10, 0, sub, MPFR_RNDN);
            fprintf(f, "\n");
        }
    }

    printf("\nsample %ld/%ld (100%% complete)\n", count, count);
}
