#include <stdio.h>
#include <stdlib.h>

#include <fenv.h>
#include <stdint.h>

#include <gmp.h>
#include <mpfr.h>

#include "nums.h"

#define TRUE 1
#define FALSE 0

// :pre (and (<= -100 u 100) (<= 20 v 20000) (<= -30 T 50))
double doppler1(double u, double v, double T) {
	double t1 = 331.4 + (0.6 * T);
	return (-t1 * v) / ((t1 + u) * (t1 + u));
}

void doppler1_mpfr(mpfr_t u, mpfr_t v, mpfr_t T, mpfr_t out, int prec) {
    mpfr_t t1, i1;
    mpfr_inits2(prec, t1, i1, NULL);
    mpfr_mul_d(t1, T, 0.6, MPFR_RNDN);
    mpfr_add_d(t1, t1, 331.4, MPFR_RNDN);

    mpfr_add(out, t1, u, MPFR_RNDN);    // (t1 + u)
    mpfr_mul(out, out, out, MPFR_RNDN); // (t1 + u) * (t1 + u)
    mpfr_mul(i1, t1, v, MPFR_RNDN);     // t1 * v
    mpfr_mul_d(i1, i1, -1, MPFR_RNDN);  // -t1 * v
    mpfr_div(out, i1, out, MPFR_RNDN);  // (-t1 * v) / ((t1 + u) * (t1 + u))

    mpfr_clears(t1, i1, NULL);
}

void test_doppler1(int prec, int samples, gmp_randstate_t rstate) {
    double u, v, T, out_dbl;
    mpfr_t um, um_lb, um_ub, vm, vm_lb, vm_ub, Tm, Tm_lb, Tm_ub, out_mpfr, err;
    mpfr_inits2(prec, um, um_lb, um_ub, vm, vm_lb, vm_ub, Tm, Tm_lb, Tm_ub, out_mpfr, err, NULL);

    FILE * f = fopen("doppler1.csv", "w");
    if (f == NULL) {
        printf("Error opening doppler1.csv\n");
        exit(1);
    }

    mpfr_set_d(um_lb, -100, MPFR_RNDN);
    mpfr_set_d(um_ub, 100, MPFR_RNDN);
    mpfr_set_d(vm_lb, 20, MPFR_RNDN);
    mpfr_set_d(vm_ub, 20000, MPFR_RNDN);
    mpfr_set_d(Tm_lb, -30, MPFR_RNDN);
    mpfr_set_d(Tm_ub, 50, MPFR_RNDN);

    fprintf(f,"u_dbl,v_dbl,T_dbl,u_mpfr,v_mpfr,T_mpfr,out_dbl,out_mpfr,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {
        if (i % 100 == 0) {
            printf("doppler1: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(um, um_lb, um_ub, prec, rstate);
        rand_mpfr(vm, vm_lb, vm_ub, prec, rstate);
        rand_mpfr(Tm, Tm_lb, Tm_ub, prec, rstate);

        u = mpfr_get_d(um, MPFR_RNDN);
        v = mpfr_get_d(vm, MPFR_RNDN);
        T = mpfr_get_d(Tm, MPFR_RNDN);

        // run both
        out_dbl = doppler1(u, v, T);
        doppler1_mpfr(um, vm, Tm, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f, %f, %f,", u, v, T);
        mpfr_out_str(f, 10, 0, um, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, vm, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, Tm, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");

    }
    printf("doppler1: sample %d/%d = (100%% complete)\n", samples, samples);

    mpfr_clears(um, um_lb, um_ub, vm, vm_lb, vm_ub, Tm, Tm_lb, Tm_ub, out_mpfr, err, NULL);
}

// :pre (and (<= -15 x1 15) (<= -15 x2 15) (<= -15 x3 15))
double rigidBody1(double x1, double x2, double x3) {
	return ((-(x1 * x2) - ((2.0 * x2) * x3)) - x1) - x3;
}

void rigidBody1_mpfr(mpfr_t x1, mpfr_t x2, mpfr_t x3, mpfr_t out, int prec) {
    mpfr_t i1, i2;
    mpfr_inits2(prec, i1, i2, NULL);

	//return ((-(x1 * x2) - ((2.0 * x2) * x3)) - x1) - x3;

    mpfr_mul_d(i1, x2, 2.0, MPFR_RNDN);  // 2.0 * x2
    mpfr_mul(i1, i1, x3, MPFR_RNDN);     // ((2.0 * x2) * x3)
    mpfr_mul(i2, x1, x2, MPFR_RNDN);     // (x1 * x2)
    mpfr_mul_d(i2, i2, -1.0, MPFR_RNDN); // -(x1 * x2)
    mpfr_sub(i1, i2, i1, MPFR_RNDN);     // (-(x1 * x2) - ((2.0 * x2) * x3))
    mpfr_sub(i1, i1, x1, MPFR_RNDN);     // (((2.0 * x2) * x3) - x1)
    mpfr_sub(out, i1, x3, MPFR_RNDN);    //((-(x1 * x2) - ((2.0 * x2) * x3)) - x1) - x3;

    mpfr_clears(i1, i2, NULL);
}

void test_rigidBody1(int prec, int samples, gmp_randstate_t rstate) {
    double x1, x2, x3, out_dbl;
    mpfr_t x1m, x1m_lb, x1m_ub, x2m, x2m_lb, x2m_ub, x3m, x3m_lb, x3m_ub, out_mpfr, err;
    mpfr_inits2(prec, x1m, x1m_lb, x1m_ub, x2m, x2m_lb, x2m_ub, x3m, x3m_lb, x3m_ub, out_mpfr, err, NULL);

    FILE * f = fopen("rigidbody1.csv", "w");
    if (f == NULL) {
        printf("Error opening rigidbody1.csv\n");
        exit(1);
    }

    mpfr_set_d(x1m_lb, -15, MPFR_RNDN);
    mpfr_set_d(x1m_ub, 15, MPFR_RNDN);
    mpfr_set_d(x2m_lb, -15, MPFR_RNDN);
    mpfr_set_d(x2m_ub, 15, MPFR_RNDN);
    mpfr_set_d(x3m_lb, -15, MPFR_RNDN);
    mpfr_set_d(x3m_ub, 15, MPFR_RNDN);

    fprintf(f,"x1_dbl,x2_dbl,x3_dbl,x1_mpfr,x2_mpfr,x3_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {
        if (i % 100 == 0) {
            printf("rigidBody1: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;
        // generate random for each parameter
        rand_mpfr(x1m, x1m_lb, x1m_ub, prec, rstate);
        rand_mpfr(x2m, x2m_lb, x2m_ub, prec, rstate);
        rand_mpfr(x3m, x3m_lb, x3m_ub, prec, rstate);

        x1 = mpfr_get_d(x1m, MPFR_RNDN);
        x2 = mpfr_get_d(x2m, MPFR_RNDN);
        x3 = mpfr_get_d(x3m, MPFR_RNDN);

        // run both
        out_dbl = rigidBody1(x1, x2, x3);
        rigidBody1_mpfr(x1m, x2m, x3m, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f, %f, %f,", x1, x2, x3);
        mpfr_out_str(f, 10, 0, x1m, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, x2m, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, x3m, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }
    printf("rigidBody1: sample %d/%d = (100%% complete)\n", samples, samples);;

    mpfr_clears(x1m, x1m_lb, x1m_ub, x2m, x2m_lb, x2m_ub, x3m, x3m_lb, x3m_ub, out_mpfr, err, NULL);
}

// :pre (and (<= -15 x1 15) (<= -15 x2 15) (<= -15 x3 15))
double rigidBody2(double x1, double x2, double x3) {
    return ((((((2.0 * x1) * x2) * x3) + ((3.0 * x3) * x3)) - (((x2 * x1) * x2) * x3)) + ((3.0 * x3) * x3)) - x2;
}

void rigidBody2_mpfr(mpfr_t x1, mpfr_t x2, mpfr_t x3, mpfr_t out, int prec) {
    mpfr_t i1, i2, i3, i4, i5, i6;
    mpfr_inits2(prec, i1, i2, i3, i4, i5, i6, NULL);

    /*
    int i1 = ((2.0 * x1) * x2) * x3;
    int i2 = (3.0 * x3) * x3
    int i3 = i1 + i2
    int i4 = ((x2 * x1) * x2) * x3
    int i5 = i3 - i4
    int i6 = (3.0 * x3) * x3
    out = i5 + i6
    out = out - x2
    */

    mpfr_mul_d(i1, x1, 2.0, MPFR_RNDN); // 2.0 * x1
    mpfr_mul(i1, i1, x2, MPFR_RNDN);    // ((2.0 * x1) * x2)
    mpfr_mul(i1, i1, x3, MPFR_RNDN);    // (((2.0 * x1) * x2) * x3)

    mpfr_mul_d(i2, x3, 3.0, MPFR_RNDN); // (3.0 * x3)
    mpfr_mul(i2, i2, x3, MPFR_RNDN);    // ((3.0 * x3) * x3)

    mpfr_add(i3, i1, i2, MPFR_RNDN);

    mpfr_mul(i4, x2, x1, MPFR_RNDN); // x2 * x1
    mpfr_mul(i4, i4, x2, MPFR_RNDN); // (x2 * x1) * x2
    mpfr_mul(i4, i4, x3, MPFR_RNDN); // ((x2 * x1) * x2) * x3

    mpfr_sub(i5, i3, i4, MPFR_RNDN);

    mpfr_mul_d(i6, x3, 3.0, MPFR_RNDN); // (3.0 * x3)
    mpfr_mul(i6, i6, x3, MPFR_RNDN);    // ((3.0 * x3) * x3)

    mpfr_add(out, i5, i6, MPFR_RNDN);
    mpfr_sub(out, out, x2, MPFR_RNDN);

    mpfr_clears(i1, i2, i3, i4, i5, i6, NULL);
}

void test_rigidBody2(int prec, int samples, gmp_randstate_t rstate) {
    double x1, x2, x3, out_dbl;
    mpfr_t x1m, x1m_lb, x1m_ub, x2m, x2m_lb, x2m_ub, x3m, x3m_lb, x3m_ub, out_mpfr, err;
    mpfr_inits2(prec, x1m, x1m_lb, x1m_ub, x2m, x2m_lb, x2m_ub, x3m, x3m_lb, x3m_ub, out_mpfr, err, NULL);

    FILE * f = fopen("rigidbody2.csv", "w");
    if (f == NULL) {
        printf("Error opening rigidbody2.csv\n");
        exit(1);
    }
    
    mpfr_set_d(x1m_lb, -15, MPFR_RNDN);
    mpfr_set_d(x1m_ub, 15, MPFR_RNDN);
    mpfr_set_d(x2m_lb, -15, MPFR_RNDN);
    mpfr_set_d(x2m_ub, 15, MPFR_RNDN);
    mpfr_set_d(x3m_lb, -15, MPFR_RNDN);
    mpfr_set_d(x3m_ub, 15, MPFR_RNDN);

    fprintf(f,"x1_dbl,x2_dbl,x3_dbl,x1_mpfr,x2_mpfr,x3_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {

        if (i % 100 == 0) {
            printf("rigidBody2: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(x1m, x1m_lb, x1m_ub, prec, rstate);
        rand_mpfr(x2m, x2m_lb, x2m_ub, prec, rstate);
        rand_mpfr(x3m, x3m_lb, x3m_ub, prec, rstate);

        x1 = mpfr_get_d(x1m, MPFR_RNDN);
        x2 = mpfr_get_d(x2m, MPFR_RNDN);
        x3 = mpfr_get_d(x3m, MPFR_RNDN);

        // run both
        out_dbl = rigidBody2(x1, x2, x3);
        rigidBody2_mpfr(x1m, x2m, x3m, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f, %f, %f,", x1, x2, x3);
        mpfr_out_str(f, 10, 0, x1m, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, x2m, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, x3m, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }

    printf("rigidBody2: sample %d/%d = (100%% complete)\n", samples, samples);;
    mpfr_clears(x1m, x1m_lb, x1m_ub, x2m, x2m_lb, x2m_ub, x3m, x3m_lb, x3m_ub, out_mpfr, err, NULL);
}

// :pre (and (<= -5 x1 5) (<= -20 x2 5))
double jetEngine(double x1, double x2) {
	double t =     (((3.0 * x1) * x1) + (2.0 * x2)) - x1;
	double t_42_ = (((3.0 * x1) * x1) - (2.0 * x2)) - x1;
	double d = (x1 * x1) + 1.0;
	double s = t / d;
	double s_42_ = t_42_ / d;
    return x1 + (((((((((2.0 * x1) * s) * (s - 3.0)) + ((x1 * x1) * ((4.0 * s)
    - 6.0))) * d) + (((3.0 * x1) * x1) * s)) + ((x1 * x1) * x1)) + x1) + (3.0 *
    s_42_));
}

void jetEngine_mpfr(mpfr_t x1, mpfr_t x2, mpfr_t out, int prec) {
    // intermediate vars
    mpfr_t i1, i2, i3, i4, i5;
    mpfr_inits2(prec, i1, i2, i3, i4, i5, NULL);

    // vars
    mpfr_t t, t_42_, d, s, s_42_;
    mpfr_inits2(prec, t, t_42_, d, s, s_42_, NULL);

    // t
    mpfr_mul_d(t, x1, 3.0, MPFR_RNDN);  // (3.0 * x1)
    mpfr_mul(t, t, x1, MPFR_RNDN);      // ((3.0 * x1) * x1)
    mpfr_mul_d(i1, x2, 2.0, MPFR_RNDN); // (2.0 * x2)
    mpfr_add(t, t, i1, MPFR_RNDN);      // ((3.0 * x1) * x1) + (2.0 * x2)
    mpfr_sub(t, t, x1, MPFR_RNDN);      // ((3.0 * x1) * x1) + (2.0 * x2) - x1

    // t_42_
    mpfr_mul_d(t_42_, x1, 3.0, MPFR_RNDN); // (3.0 * x1)
    mpfr_mul(t_42_, t_42_, x1, MPFR_RNDN); // ((3.0 * x1) * x1)
    mpfr_mul_d(i1, x2, 2.0, MPFR_RNDN);    // (2.0 * x2)
    mpfr_sub(t_42_, t_42_, i1, MPFR_RNDN); // ((3.0 * x1) * x1) - (2.0 * x2)
    mpfr_sub(t_42_, t_42_, x1, MPFR_RNDN); // ((3.0 * x1) * x1) - (2.0 * x2) - x1

    // d
    mpfr_mul(d, x1, x1, MPFR_RNDN);   // x1 * x1
    mpfr_add_d(d, d, 1.0, MPFR_RNDN); // (x1 * x1) + 1.0
        
    // s
    mpfr_div(s, t, d, MPFR_RNDN);     // t / d

    // s_42_
    mpfr_div(s_42_, t_42_, d, MPFR_RNDN);

    /*(
     * return x1 + (((((((((2.0 * x1) * s) * (s - 3.0)) + ((x1 * x1) * ((4.0 * s)
     * - 6.0))) * d) + (((3.0 * x1) * x1) * s)) + ((x1 * x1) * x1)) + x1) + (3.0 *
     * s_42_));
     */

    mpfr_mul_d(i1, x1, 2.0, MPFR_RNDN);    // i1 = (2.0 * x1)
    mpfr_mul(i1, i1, s, MPFR_RNDN);        // i1 = i1 * s
    mpfr_sub_d(i2, s, 3.0, MPFR_RNDN);     // i2 = s - 3.0
    mpfr_mul(i3, i1, i2, MPFR_RNDN);       // i3 = i1 * i2
    mpfr_mul(i4, x1, x1, MPFR_RNDN);       // i4 = x1 * x1
    mpfr_mul_d(i5, s, 4.0, MPFR_RNDN);     // i5 = 4.0 * s
    mpfr_sub_d(i5, i5, 6.0, MPFR_RNDN);    // i5 = i5 - 6.0
    mpfr_mul(i4, i4, i5, MPFR_RNDN);       // i4 = i4 * i5
    mpfr_add(i3, i3, i4, MPFR_RNDN);       // i3 = i3 + i4
    mpfr_mul(i3, i3, d, MPFR_RNDN);        // i3 = i3 * d
    mpfr_mul_d(i1, x1, 3.0, MPFR_RNDN);    // i1 = 3.0 * x1
    mpfr_mul(i1, i1, x1, MPFR_RNDN);       // i1 = i1 * x1
    mpfr_mul(i1, i1, s, MPFR_RNDN);        // i1 = i1 * s
    mpfr_add(i1, i1, i3, MPFR_RNDN);       // i1 = i1 + i3
    mpfr_mul(i2, x1, x1, MPFR_RNDN);       // i2 = x1 * x1
    mpfr_mul(i2, i2, x1, MPFR_RNDN);       // i2 = i2 * x1
    mpfr_add(i1, i1, i2, MPFR_RNDN);       // i1 = i1 + i2
    mpfr_add(i1, i1, x1, MPFR_RNDN);       // i1 = i1 + x1
    mpfr_mul_d(i2, s_42_, 3.0, MPFR_RNDN); // i2 = 3.0 * s_42_
    mpfr_add(i1, i1, i2, MPFR_RNDN);       // i1 = i1 + i2
    mpfr_add(out, x1, i1, MPFR_RNDN);      // out = x1 + i1

    mpfr_clears(i1, i2, i3, i4, i5, NULL);
    mpfr_clears(t, t_42_, d, s, s_42_, NULL);
}

void test_jetEngine(int prec, int samples, gmp_randstate_t rstate) {
    double x1, x2, out_dbl;
    mpfr_t x1m, x1m_lb, x1m_ub, x2m, x2m_lb, x2m_ub, out_mpfr, err;
    mpfr_inits2(prec, x1m, x1m_lb, x1m_ub, x2m, x2m_lb, x2m_ub, out_mpfr, err, NULL);

    FILE * f = fopen("jetEngine.csv", "w");
    if (f == NULL) {
        printf("Error opening jetEngine.csv\n");
        exit(1);
    }

    mpfr_set_d(x1m_lb, -5, MPFR_RNDN);
    mpfr_set_d(x1m_ub, 5, MPFR_RNDN);
    mpfr_set_d(x2m_lb, -20, MPFR_RNDN);
    mpfr_set_d(x2m_ub, 5, MPFR_RNDN);

    fprintf(f,"x1_dbl,x2_dbl,x1_mpfr,x2_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {

        if (i % 100 == 0) {
            printf("jetEngine: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(x1m, x1m_lb, x1m_ub, prec, rstate);
        rand_mpfr(x2m, x2m_lb, x2m_ub, prec, rstate);

        x1 = mpfr_get_d(x1m, MPFR_RNDN);
        x2 = mpfr_get_d(x2m, MPFR_RNDN);

        // run both
        out_dbl = jetEngine(x1, x2);
        jetEngine_mpfr(x1m, x2m, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f, %f,", x1, x2);
        mpfr_out_str(f, 10, 0, x1m, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, x2m, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }

    printf("jetEngine: sample %d/%d = (100%% complete)\n", samples, samples);
    mpfr_clears(x1m, x1m_lb, x1m_ub, x2m, x2m_lb, x2m_ub, out_mpfr, err, NULL);
}

// :pre (and (<= -4.5 v -0.3) (<= 0.4 w 0.9) (<= 3.8 r 7.8))
double turbine1(double v, double w, double r) {
    return ((3.0 + (2.0 / (r * r))) - (((0.125 * (3.0 - (2.0 * v))) * (((w * w)
    * r) * r)) / (1.0 - v))) - 4.5;
}

void turbine1_mpfr(mpfr_t v, mpfr_t w, mpfr_t r, mpfr_t out, int prec) {
    mpfr_t i1, i2, i3;
    mpfr_inits2(prec, i1, i2, i3, NULL);
    /*
     *  return ((3.0 + (2.0 / (r * r))) - (((0.125 * (3.0 - (2.0 * v))) * (((w * w)
     *  * r) * r)) / (1.0 - v))) - 4.5;
     */

    mpfr_mul(i1, r, r, MPFR_RNDN); // i1 = r * r
    mpfr_d_div(i1, 2.0, i1, MPFR_RNDN); // i1 = 2.0 / (r * r)
    mpfr_add_d(i1, i1, 3.0, MPFR_RNDN); // i1 = 3.0 + (2.0 / (r * r))
    mpfr_mul_d(i2, v, 2.0, MPFR_RNDN);  // i2 = 2.0 * v
    mpfr_d_sub(i2, 3.0, i2, MPFR_RNDN); // i2 = 3.0 - (2.0 * v)
    mpfr_mul_d(i2, i2, 0.125, MPFR_RNDN); // i2 = 0.125 * (3.0 - (2.0 * v))
    mpfr_mul(i3, w, w, MPFR_RNDN); // i3 = w * w
    mpfr_mul(i3, i3, r, MPFR_RNDN); // i3 = (w * w) * r
    mpfr_mul(i3, i3, r, MPFR_RNDN); // i3 = ((w * w) * r) * r
    mpfr_mul(i2, i2, i3, MPFR_RNDN); // i2 = i2 * i3
    mpfr_d_sub(i3, 1.0, v, MPFR_RNDN); // i3 = 1.0 - v
    mpfr_div(i2, i2, i3, MPFR_RNDN); // i2 = i2 / i3
    mpfr_sub(i1, i1, i2, MPFR_RNDN); // i1 = i1 - i2
    mpfr_sub_d(out, i1, 4.5, MPFR_RNDN); // out = i1 - 4.5

    mpfr_clears(i1, i2, i3, NULL);
}

void test_turbine1(int prec, int samples, gmp_randstate_t rstate) {
    double v, w, r, out_dbl;
    mpfr_t vm, vm_lb, vm_ub, wm, wm_lb, wm_ub, rm, rm_lb, rm_ub, out_mpfr, err;
    mpfr_inits2(prec, vm, vm_lb, vm_ub, wm, wm_lb, wm_ub, rm, rm_lb, rm_ub, out_mpfr, err, NULL);

    FILE * f = fopen("turbine1.csv", "w");
    if (f == NULL) {
        printf("Error opening turbine1.csv\n");
        exit(1);
    }

    mpfr_set_d(vm_lb, -4.5, MPFR_RNDN);
    mpfr_set_d(vm_ub, -0.3, MPFR_RNDN);
    mpfr_set_d(wm_lb, 0.4, MPFR_RNDN);
    mpfr_set_d(wm_ub, 0.9, MPFR_RNDN);
    mpfr_set_d(rm_lb, 3.8, MPFR_RNDN);
    mpfr_set_d(rm_ub, 7.8, MPFR_RNDN);

    fprintf(f,"v_dbl,w_dbl,r_dbl,v_mpfr,w_mpfr,r_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {

        if (i % 100 == 0) {
            printf("turbine1: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(vm, vm_lb, vm_ub, prec, rstate);
        rand_mpfr(wm, wm_lb, wm_ub, prec, rstate);
        rand_mpfr(rm, rm_lb, rm_ub, prec, rstate);

        v = mpfr_get_d(vm, MPFR_RNDN);
        w = mpfr_get_d(wm, MPFR_RNDN);
        r = mpfr_get_d(rm, MPFR_RNDN);

        // run both
        out_dbl = turbine1(v, w, r);
        turbine1_mpfr(vm, wm, rm, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f, %f, %f,", v, w, r);
        mpfr_out_str(f, 10, 0, vm, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, wm, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, rm, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }
    printf("turbine1: sample %d/%d = (100%% complete)\n", samples, samples);

    mpfr_clears(vm, vm_lb, vm_ub, wm, wm_lb, wm_ub, rm, rm_lb, rm_ub, out_mpfr, err, NULL);
}

// :pre (and (<= -4.5 v -0.3) (<= 0.4 w 0.9) (<= 3.8 r 7.8))
double turbine2(double v, double w, double r) {
	return ((6.0 * v) - (((0.5 * v) * (((w * w) * r) * r)) / (1.0 - v))) - 2.5;
}

void turbine2_mpfr(mpfr_t v, mpfr_t w, mpfr_t r, mpfr_t out, int prec) {

    mpfr_t i1, i2, i3;
    mpfr_inits2(prec, i1, i2, i3, NULL);

    mpfr_mul_d(i1, v, 6.0, MPFR_RNDN); // i1 = 6.0 * v
    mpfr_mul_d(i2, v, 0.5, MPFR_RNDN); // i2 = 0.5 * v
    mpfr_mul(i3, w, w, MPFR_RNDN); // i3 = w * w
    mpfr_mul(i3, i3, r, MPFR_RNDN); // i3 = i3 * r
    mpfr_mul(i3, i3, r, MPFR_RNDN); // i3 = i3 * r
    mpfr_mul(i2, i2, i3, MPFR_RNDN); // i2 = i2 * i3
    mpfr_d_sub(i3, 1.0, v, MPFR_RNDN); // i3 = 1.0 - v
    mpfr_div(i2, i2, i3, MPFR_RNDN); // i2 = i2 / i3
    mpfr_sub(i1, i1, i2, MPFR_RNDN); // i1 = i1 - i2
    mpfr_sub_d(out, i1, 2.5, MPFR_RNDN); // out = i1 - 2.5
    
    mpfr_clears(i1, i2, i3, NULL);
}

void test_turbine2(int prec, int samples, gmp_randstate_t rstate) {
    double v, w, r, out_dbl;
    mpfr_t vm, vm_lb, vm_ub, wm, wm_lb, wm_ub, rm, rm_lb, rm_ub, out_mpfr, err;
    mpfr_inits2(prec, vm, vm_lb, vm_ub, wm, wm_lb, wm_ub, rm, rm_lb, rm_ub, out_mpfr, err, NULL);

    FILE * f = fopen("turbine2.csv", "w");
    if (f == NULL) {
        printf("Error opening turbine2.csv\n");
        exit(1);
    }

    mpfr_set_d(vm_lb, -4.5, MPFR_RNDN);
    mpfr_set_d(vm_ub, -0.3, MPFR_RNDN);
    mpfr_set_d(wm_lb, 0.4, MPFR_RNDN);
    mpfr_set_d(wm_ub, 0.9, MPFR_RNDN);
    mpfr_set_d(rm_lb, 3.8, MPFR_RNDN);
    mpfr_set_d(rm_ub, 7.8, MPFR_RNDN);

    fprintf(f,"v_dbl,w_dbl,r_dbl,v_mpfr,w_mpfr,r_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {

        if (i % 100 == 0) {
            printf("turbine2: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(vm, vm_lb, vm_ub, prec, rstate);
        rand_mpfr(wm, wm_lb, wm_ub, prec, rstate);
        rand_mpfr(rm, rm_lb, rm_ub, prec, rstate);

        v = mpfr_get_d(vm, MPFR_RNDN);
        w = mpfr_get_d(wm, MPFR_RNDN);
        r = mpfr_get_d(rm, MPFR_RNDN);

        // run both
        out_dbl = turbine2(v, w, r);
        turbine2_mpfr(vm, wm, rm, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f, %f, %f,", v, w, r);
        mpfr_out_str(f, 10, 0, vm, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, wm, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, rm, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }
    printf("turbine2: sample %d/%d = (100%% complete)\n", samples, samples);

    mpfr_clears(vm, vm_lb, vm_ub, wm, wm_lb, wm_ub, rm, rm_lb, rm_ub, out_mpfr, err, NULL);
}

// :pre (and (<= -4.5 v -0.3) (<= 0.4 w 0.9) (<= 3.8 r 7.8))
double turbine3(double v, double w, double r) {
	return ((3.0 - (2.0 / (r * r))) - (((0.125 * (1.0 + (2.0 * v))) * (((w * w) * r) * r)) / (1.0 - v))) - 0.5;
}

void turbine3_mpfr(mpfr_t v, mpfr_t w, mpfr_t r, mpfr_t out, int prec) {
    mpfr_t i1, i2, i3;
    mpfr_inits2(prec, i1, i2, i3, NULL);

    mpfr_mul(i1, r, r, MPFR_RNDN); // i1 = r * r
    mpfr_d_div(i1, 2.0, i1, MPFR_RNDN); // i1 = 2.0 / i1
    mpfr_d_sub(i1, 3.0, i1, MPFR_RNDN); // i1 = 3.0 - i1
    mpfr_mul_d(i2, v, 2.0, MPFR_RNDN); // i2 = 2.0 * v
    mpfr_add_d(i2, i2, 1.0, MPFR_RNDN); // i2 = 1.0 + i2
    mpfr_mul_d(i2, i2, 0.125, MPFR_RNDN); // i2 = 0.125 * i2
    mpfr_mul(i3, w, w, MPFR_RNDN); // i3 = w * w
    mpfr_mul(i3, i3, r, MPFR_RNDN); // i3 = i3 * r
    mpfr_mul(i3, i3, r, MPFR_RNDN); // i3 = i3 * r
    mpfr_mul(i2, i2, i3, MPFR_RNDN); // i2 = i2 * i3
    mpfr_d_sub(i3, 1.0, v, MPFR_RNDN); // i3 = 1.0 - v
    mpfr_div(i2, i2, i3, MPFR_RNDN); // i2 = i2 / i3
    mpfr_sub(i1, i1, i2, MPFR_RNDN); // i1 = i1 - i2
    mpfr_sub_d(out, i1, 0.5, MPFR_RNDN); // out = i1 - 0.5

    mpfr_clears(i1, i2, i3, NULL);
}

void test_turbine3(int prec, int samples, gmp_randstate_t rstate) {
    double v, w, r, out_dbl;
    mpfr_t vm, vm_lb, vm_ub, wm, wm_lb, wm_ub, rm, rm_lb, rm_ub, out_mpfr, err;
    mpfr_inits2(prec, vm, vm_lb, vm_ub, wm, wm_lb, wm_ub, rm, rm_lb, rm_ub, out_mpfr, err, NULL);

    FILE * f = fopen("turbine3.csv", "w");
    if (f == NULL) {
        printf("Error opening turbine3.csv\n");
        exit(1);
    }

    mpfr_set_d(vm_lb, -4.5, MPFR_RNDN);
    mpfr_set_d(vm_ub, -0.3, MPFR_RNDN);
    mpfr_set_d(wm_lb, 0.4, MPFR_RNDN);
    mpfr_set_d(wm_ub, 0.9, MPFR_RNDN);
    mpfr_set_d(rm_lb, 3.8, MPFR_RNDN);
    mpfr_set_d(rm_ub, 7.8, MPFR_RNDN);

    fprintf(f,"v_dbl,w_dbl,r_dbl,v_mpfr,w_mpfr,r_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {

        if (i % 100 == 0) {
            printf("turbine3: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(vm, vm_lb, vm_ub, prec, rstate);
        rand_mpfr(wm, wm_lb, wm_ub, prec, rstate);
        rand_mpfr(rm, rm_lb, rm_ub, prec, rstate);

        v = mpfr_get_d(vm, MPFR_RNDN);
        w = mpfr_get_d(wm, MPFR_RNDN);
        r = mpfr_get_d(rm, MPFR_RNDN);

        // run both
        out_dbl = turbine3(v, w, r);
        turbine3_mpfr(vm, wm, rm, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f, %f, %f,", v, w, r);
        mpfr_out_str(f, 10, 0, vm, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, wm, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, rm, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }
    printf("turbine3: sample %d/%d = (100%% complete)\n", samples, samples);

    mpfr_clears(vm, vm_lb, vm_ub, wm, wm_lb, wm_ub, rm, rm_lb, rm_ub, out_mpfr, err, NULL);
}

// :pre (<= 0.1 x 0.3)
double verhulst(double x) {
	double r = 4.0;
	double K = 1.11;
	return (r * x) / (1.0 + (x / K));
}

void verhulst_mpfr(mpfr_t x, mpfr_t out, int prec) {
    mpfr_t r, K, i1, i2;
    mpfr_inits2(prec, r, K, i1, i2, NULL);

    mpfr_set_d(r, 4.0, MPFR_RNDN);
    mpfr_set_d(K, 1.11, MPFR_RNDN);

    mpfr_mul(i1, r, x, MPFR_RNDN);
    mpfr_div(i2, x, K, MPFR_RNDN);
    mpfr_add_d(i2, i2, 1.0, MPFR_RNDN);
    mpfr_div(out, i1, i2, MPFR_RNDN);

    mpfr_clears(r, K, i1, i2, NULL);
}

void test_verhulst(int prec, int samples, gmp_randstate_t rstate) {
    double x, out_dbl;
    mpfr_t xm, xm_lb, xm_ub, out_mpfr, err;
    mpfr_inits2(prec, xm, xm_lb, xm_ub, out_mpfr, err, NULL);

    FILE * f = fopen("verhulst.csv", "w");
    if (f == NULL) {
        printf("Error opening verhulst.csv\n");
        exit(1);
    }

    mpfr_set_d(xm_lb, 0.1, MPFR_RNDN);
    mpfr_set_d(xm_ub, 0.3, MPFR_RNDN);

    fprintf(f,"x_dbl,x_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {

        if (i % 100 == 0) {
            printf("verhulst: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(xm, xm_lb, xm_ub, prec, rstate);

        x = mpfr_get_d(xm, MPFR_RNDN);

        // run both
        out_dbl = verhulst(x);
        verhulst_mpfr(xm, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f,", x);
        mpfr_out_str(f, 10, 0, xm, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }
    printf("verhulst: sample %d/%d = (100%% complete)\n", samples, samples);

    mpfr_clears(xm, xm_lb, xm_ub, out_mpfr, err, NULL);
}

// :pre (<= 0.1 x 0.3)
double predatorPrey(double x) {
	double r = 4.0;
	double K = 1.11;
	return ((r * x) * x) / (1.0 + ((x / K) * (x / K)));
}

void predatorPrey_mpfr(mpfr_t x, mpfr_t out, int prec) {
    mpfr_t r, K, i1, i2, i3;
    mpfr_inits2(prec, r, K, i1, i2, i3, NULL);

    mpfr_set_d(r, 4.0, MPFR_RNDN);
    mpfr_set_d(K, 1.11, MPFR_RNDN);

    mpfr_mul(i1, r, x, MPFR_RNDN);
    mpfr_mul(i1, i1, x, MPFR_RNDN);
    mpfr_div(i2, x, K, MPFR_RNDN);
    mpfr_div(i3, x, K, MPFR_RNDN);
    mpfr_mul(i2, i2, i3, MPFR_RNDN);
    mpfr_add_d(i2, i2, 1.0, MPFR_RNDN);
    mpfr_div(out, i1, i2, MPFR_RNDN);

    mpfr_clears(r, K, i1, i2, i3, NULL);
}

void test_predatorPrey(int prec, int samples, gmp_randstate_t rstate) {
    double x, out_dbl;
    mpfr_t xm, xm_lb, xm_ub, out_mpfr, err;
    mpfr_inits2(prec, xm, xm_lb, xm_ub, out_mpfr, err, NULL);

    FILE * f = fopen("predatorPrey.csv", "w");
    if (f == NULL) {
        printf("Error opening predatorPrey.csv\n");
        exit(1);
    }

    mpfr_set_d(xm_lb, 0.1, MPFR_RNDN);
    mpfr_set_d(xm_ub, 0.3, MPFR_RNDN);

    fprintf(f, "x_dbl,x_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {

        if (i % 100 == 0) {
            printf("predatorPrey: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(xm, xm_lb, xm_ub, prec, rstate);

        x = mpfr_get_d(xm, MPFR_RNDN);

        // run both
        out_dbl = predatorPrey(x);
        predatorPrey_mpfr(xm, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f,", x);
        mpfr_out_str(f, 10, 0, xm, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }
    printf("predatorPrey: sample %d/%d = (100%% complete)\n", samples, samples);

    mpfr_clears(xm, xm_lb, xm_ub, out_mpfr, err, NULL);
}

//  :pre (<= 0.1 v 0.5)
double carbonGas(double v) {
	double p = 35000000.0;
	double a = 0.401;
	double b = 4.27e-5;
	double t = 300.0;
	double n = 1000.0;
	double k = 1.3806503e-23;
	return ((p + ((a * (n / v)) * (n / v))) * (v - (n * b))) - ((k * n) * t);
}

void carbonGas_mpfr(mpfr_t v, mpfr_t out, int prec) {
    mpfr_t p, a, b, t, n, k, i1, i2;
    mpfr_inits2(prec, p, a, b, t, n, k, i1, i2, NULL);

    mpfr_set_d(p, 35000000.0, MPFR_RNDN);
    mpfr_set_d(a, 0.401, MPFR_RNDN);
    mpfr_set_d(b, 4.27e-5, MPFR_RNDN);
    mpfr_set_d(t, 300.0, MPFR_RNDN);
    mpfr_set_d(n, 1000.0, MPFR_RNDN);
    mpfr_set_d(k, 1.3806503e-23, MPFR_RNDN);

    mpfr_div(i1, n, v, MPFR_RNDN);     // i1 = n / v
    mpfr_mul(i1, a, i1, MPFR_RNDN);    // i1 = a * i1
    mpfr_div(i2, n, v, MPFR_RNDN);     // i2 = n / v
    mpfr_mul(i1, i1, i2, MPFR_RNDN);   // i1 = i1 * i2
    mpfr_add(i1, p, i1, MPFR_RNDN);    // i1 = p + i1
    mpfr_mul(i2, n, b, MPFR_RNDN);     // i2 = n * b
    mpfr_sub(i2, v, i2, MPFR_RNDN);    // i2 = v - i2
    mpfr_mul(i1, i1, i2, MPFR_RNDN);   // i1 = i1 * i2
    mpfr_mul(i2, k, n, MPFR_RNDN);     // i2 = k * n
    mpfr_mul(i2, i2, t, MPFR_RNDN);    // i2 = i2 * t
    mpfr_sub(out, i1, i2, MPFR_RNDN);  // out = i1 - i2

    mpfr_clears(p, a, b, t, n, k, i1, i2, NULL);
}

void test_carbonGas(int prec, int samples, gmp_randstate_t rstate) {
    double v, out_dbl;
    mpfr_t vm, vm_lb, vm_ub, out_mpfr, err;
    mpfr_inits2(prec, vm, vm_lb, vm_ub, out_mpfr, err, NULL);

    FILE * f = fopen("carbonGas.csv", "w");
    if (f == NULL) {
        printf("Error opening carbonGas.csv\n");
        exit(1);
    }

    mpfr_set_d(vm_lb, 0.1, MPFR_RNDN);
    mpfr_set_d(vm_ub, 0.5, MPFR_RNDN);

    fprintf(f, "v_dbl,v_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {

        if (i % 100 == 0) {
            printf("carbonGas: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(vm, vm_lb, vm_ub, prec, rstate);

        v = mpfr_get_d(vm, MPFR_RNDN);

        // run both
        out_dbl = carbonGas(v);
        carbonGas_mpfr(vm, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f,", v);
        mpfr_out_str(f, 10, 0, vm, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }
    printf("carbonGas: sample %d/%d = (100%% complete)\n", samples, samples);

    mpfr_clears(vm, vm_lb, vm_ub, out_mpfr, err, NULL);
}

// :pre (<= 0 x 1)
double sqroot(double x) {
    return (((1.0 + (0.5 * x)) - ((0.125 * x) * x)) + (((0.0625 * x) * x) * x))
    - ((((0.0390625 * x) * x) * x) * x);
}

void sqroot_mpfr(mpfr_t x, mpfr_t out, int prec) {
    mpfr_t i1, i2;
    mpfr_inits2(prec, i1, i2, NULL);

    mpfr_mul_d(i1, x, 0.5, MPFR_RNDN);       // i1 = 0.5 * x
    mpfr_add_d(i1, i1, 1.0, MPFR_RNDN);      // i1 = 1.0 + i1
    mpfr_mul_d(i2, x, 0.125, MPFR_RNDN);     // i2 = 0.125 * x
    mpfr_mul(i2, i2, x, MPFR_RNDN);          // i2 = i2 * x
    mpfr_sub(i1, i1, i2, MPFR_RNDN);         // i1 = i1 - i2
    mpfr_mul_d(i2, x, 0.0625, MPFR_RNDN);    // i2 = 0.0625 * x
    mpfr_mul(i2, i2, x, MPFR_RNDN);          // i2 = i2 * x
    mpfr_mul(i2, i2, x, MPFR_RNDN);          // i2 = i2 * x
    mpfr_add(i1, i1, i2, MPFR_RNDN);         // i1 = i1 + i2
    mpfr_mul_d(i2, x, 0.0390625, MPFR_RNDN); // i2 = 0.0390625 * x
    mpfr_mul(i2, i2, x, MPFR_RNDN);          // i2 = i2 * x
    mpfr_mul(i2, i2, x, MPFR_RNDN);          // i2 = i2 * x
    mpfr_mul(i2, i2, x, MPFR_RNDN);          // i2 = i2 * x
    mpfr_sub(out, i1, i2, MPFR_RNDN);        // out = i1 - i2

    mpfr_clears(i1, i2, NULL);
}

void test_sqroot(int prec, int samples, gmp_randstate_t rstate) {
    double x, out_dbl;
    mpfr_t xm, xm_lb, xm_ub, out_mpfr, err;
    mpfr_inits2(prec, xm, xm_lb, xm_ub, out_mpfr, err, NULL);

    FILE * f = fopen("sqroot.csv", "w");
    if (f == NULL) {
        printf("Error opening sqroot.csv\n");
        exit(1);
    }

    mpfr_set_d(xm_lb, 0.1, MPFR_RNDN);
    mpfr_set_d(xm_ub, 0.3, MPFR_RNDN);

    fprintf(f, "x_dbl,x_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {

        if (i % 100 == 0) {
            printf("sqroot: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(xm, xm_lb, xm_ub, prec, rstate);

        x = mpfr_get_d(xm, MPFR_RNDN);

        // run both
        out_dbl = sqroot(x);
        sqroot_mpfr(xm, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f,", x);
        mpfr_out_str(f, 10, 0, xm, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }
    printf("sqroot: sample %d/%d = (100%% complete)\n", samples, samples);

    mpfr_clears(xm, xm_lb, xm_ub, out_mpfr, err, NULL);
}

// :pre (< -2 x 2)
double sineOrder3(double x) {
	return (0.954929658551372 * x) - (0.12900613773279798 * ((x * x) * x));
}

void sineOrder3_mpfr(mpfr_t x, mpfr_t out, int prec) {
    mpfr_t i1, i2;
    mpfr_inits2(prec, i1, i2, NULL);

    mpfr_mul_d(i1, x, 0.954929658551372, MPFR_RNDN);
    mpfr_mul(i2, x, x, MPFR_RNDN);
    mpfr_mul(i2, i2, x, MPFR_RNDN);
    mpfr_mul_d(i2, i2, 0.12900613773279798, MPFR_RNDN);
    mpfr_sub(out, i1, i2, MPFR_RNDN);

    mpfr_clears(i1, i2, NULL);
}

void test_sineOrder3(int prec, int samples, gmp_randstate_t rstate) {
    double x, out_dbl;
    mpfr_t xm, xm_lb, xm_ub, out_mpfr, err;
    mpfr_inits2(prec, xm, xm_lb, xm_ub, out_mpfr, err, NULL);

    FILE * f = fopen("sineOrder3.csv", "w");
    if (f == NULL) {
        printf("Error opening sineOrder3.csv\n");
        exit(1);
    }

    mpfr_set_d(xm_lb, -2, MPFR_RNDN);
    mpfr_set_d(xm_ub, 2, MPFR_RNDN);

    fprintf(f, "x_dbl,x_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {

        if (i % 100 == 0) {
            printf("sineOrder3: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(xm, xm_lb, xm_ub, prec, rstate);

        x = mpfr_get_d(xm, MPFR_RNDN);

        // run both
        out_dbl = sineOrder3(x);
        sineOrder3_mpfr(xm, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f,", x);
        mpfr_out_str(f, 10, 0, xm, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }
    printf("sineOrder3: sample %d/%d = (100%% complete)\n", samples, samples);

    mpfr_clears(xm, xm_lb, xm_ub, out_mpfr, err, NULL);
}

// :pre (< 0 x 10)
double cav10(double x) {
	double tmp;
	if (((x * x) - x) >= 0.0) {
		tmp = x / 10.0;
	} else {
		tmp = (x * x) + 2.0;
	}
	return tmp;
}

void cav10_mpfr(mpfr_t x, mpfr_t out, int prec) {
    mpfr_t i1;
    mpfr_inits2(prec, i1, NULL);
     
    mpfr_mul(i1, x, x, MPFR_RNDN);
    mpfr_sub(i1, i1, x, MPFR_RNDN);

    if (mpfr_cmp_d(i1, 0.0) >= 0) {
        mpfr_div_d(out, x, 10.0, MPFR_RNDN);
    } else {
        mpfr_mul(out, x, x, MPFR_RNDN);
        mpfr_add_d(out, out, 2.0, MPFR_RNDN);
    }

    mpfr_clears(i1, NULL);
}

void test_cav10(int prec, int samples, gmp_randstate_t rstate) {
    double x, out_dbl;
    mpfr_t xm, xm_lb, xm_ub, out_mpfr, err;
    mpfr_inits2(prec, xm, xm_lb, xm_ub, out_mpfr, err, NULL);

    FILE * f = fopen("cav10.csv", "w");
    if (f == NULL) {
        printf("Error opening cav10.csv\n");
        exit(1);
    }

    mpfr_set_d(xm_lb, 0, MPFR_RNDN);
    mpfr_set_d(xm_ub, 10, MPFR_RNDN);

    fprintf(f, "x_dbl,x_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {

        if (i % 100 == 0) {
            printf("cav10: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(xm, xm_lb, xm_ub, prec, rstate);

        x = mpfr_get_d(xm, MPFR_RNDN);

        // run both
        out_dbl = cav10(x);
        cav10_mpfr(xm, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f,", x);
        mpfr_out_str(f, 10, 0, xm, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }
    printf("cav10: sample %d/%d = (100%% complete)\n", samples, samples);

    mpfr_clears(xm, xm_lb, xm_ub, out_mpfr, err, NULL);
}

// :pre (<= 0 u 1)
double bspline3(double u) {
	return -((u * u) * u) / 6.0;
}

void bspline3_mpfr(mpfr_t u, mpfr_t out, int prec) {
    mpfr_mul(out, u, u, MPFR_RNDN);
    mpfr_mul(out, out, u, MPFR_RNDN);
    mpfr_mul_d(out, out, -1.0, MPFR_RNDN);
    mpfr_div_d(out, out, 6.0, MPFR_RNDN);
}

void test_bspline3(int prec, int samples, gmp_randstate_t rstate) {
    double x, out_dbl;
    mpfr_t xm, xm_lb, xm_ub, out_mpfr, err;
    mpfr_inits2(prec, xm, xm_lb, xm_ub, out_mpfr, err, NULL);

    FILE * f = fopen("bspline3.csv", "w");
    if (f == NULL) {
        printf("Error opening bspline3.csv\n");
        exit(1);
    }

    mpfr_set_d(xm_lb, 0, MPFR_RNDN);
    mpfr_set_d(xm_ub, 1, MPFR_RNDN);

    fprintf(f, "u_dbl,u_mpfr,dbl_out,mpfr_out,err\n");

    int curr = 0;

    for (int i = 0; i < samples; i++) {

        if (i % 100 == 0) {
            printf("bspline3: sample %d/%d = (%.1f%% complete)\r", curr, samples,
                   100. * ((double) curr) / ((double) samples));
        }
        curr++;

        // generate random for each parameter
        rand_mpfr(xm, xm_lb, xm_ub, prec, rstate);

        x = mpfr_get_d(xm, MPFR_RNDN);

        // run both
        out_dbl = bspline3(x);
        bspline3_mpfr(xm, out_mpfr, prec);

        // calculate error
        mpfr_sub_d(err, out_mpfr, out_dbl, MPFR_RNDN);
        mpfr_abs(err, err, MPFR_RNDN);

        // write to csv
        fprintf(f, "%f,", x);
        mpfr_out_str(f, 10, 0, xm, MPFR_RNDN); fprintf(f, ",");
        fprintf(f, "%f,", out_dbl);
        mpfr_out_str(f, 10, 0, out_mpfr, MPFR_RNDN); fprintf(f, ",");
        mpfr_out_str(f, 10, 0, err, MPFR_RNDN);
        fprintf(f, "\n");
    }
    printf("bspline3: sample %d/%d = (100%% complete)\n", samples, samples);

    mpfr_clears(xm, xm_lb, xm_ub, out_mpfr, err, NULL);
}

void test_rosa(int prec, int samples) {
    // initialize random state
    gmp_randstate_t rstate;
    gmp_randinit_mt(rstate);
    unsigned long seed;
    gmp_randseed_ui(rstate, seed);
    
    printf("test_doppler1\n");    test_doppler1(prec, samples, rstate);
    printf("test_rigidBody1\n");  test_rigidBody1(prec, samples, rstate);
    printf("test_rigidBody2\n");  test_rigidBody2(prec, samples, rstate);
    printf("test_jetEngine\n");   test_jetEngine(prec, samples, rstate);
    printf("test_turbine1\n");    test_turbine1(prec, samples, rstate);
    printf("test_turbine2\n");    test_turbine2(prec, samples, rstate);
    printf("test_turbine3\n");    test_turbine3(prec, samples, rstate);
    printf("test_verhulst\n");    test_verhulst(prec, samples, rstate);
    printf("test_predatorPrey\n"); test_predatorPrey(prec, samples, rstate);
    printf("test_carbonGas\n");    test_carbonGas(prec, samples, rstate);
    printf("test_sqroot\n");       test_sqroot(prec, samples, rstate);
    printf("test_sineOrder3\n");   test_sineOrder3(prec, samples, rstate);
    printf("test_cav10\n");        test_cav10(prec, samples, rstate);
    printf("test_bspline3\n");     test_bspline3(prec, samples, rstate);
}
