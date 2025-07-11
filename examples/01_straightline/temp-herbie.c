#include <stdio.h>
#include <gmp.h>
#include <mpfr.h>

#define MPFR_BITS 200

/* From Herbie:
 * https://herbie.uwplse.org/demo/48c674575132f70296b2d18ba2ec068068d28e0c.1a83c9f5186db102b678a2d5f869f99992469071/graph.html
 */
/* Original
 * Accuracy: 99.9%, 1.0x speedup */
double temp(double t,
		double b0, double b1, double b2, double b3, double b4, double b5,
		double s0, double s1, double s2, double s3,
		double ain)
{
	double t2 = t*t;
	double t3 = t2*t;
	double t4 = t2*t2;
	double t5 = t3*t2;
	double b = b0 + t*b1 + t2*b2 + t3*b3 + t4*b4 + t5*b5;
	double s = s0 + t*s1 + t2*s2 + t3*s3;
	return (ain - b)/s;
}

/* Alt 2: 99.4% accurate, 2.6x speedup */
double temp_alt2(double t,
		double b0, double b1, double b2, double b3, double b4, double b5,
		double s0, double s1, double s2, double s3,
		double ain)
{
	return (ain - ((t * (b1 + (t * (b2 + (t * (b3 + (b4 * t))))))) + b0)) / ((s1 * t) + s0);
}

/* Alt 7: 99.4% accurate, 5.6x speedup */
double temp_ite(double t,
		double b0, double b1, double b2, double b3, double b4, double b5,
		double s0, double s1, double s2, double s3,
		double ain)
{
	double tmp;
	if ((ain <= -7.4e-125) || !(ain <= 2e-147)) {
		tmp = ain / s0;
	} else {
		tmp = -b0 / s0;
	}
	return tmp;
}

/* Alt 7: 88.4% accurate, 9.6x speedup */
double temp_alt7(double t,
		double b0, double b1, double b2, double b3, double b4, double b5,
		double s0, double s1, double s2, double s3,
		double ain)
{
	return (ain - b0) / s0;
}

int temp_mpfr(mpfr_t *rv, double t,
		double b0, double b1, double b2, double b3, double b4, double b5,
		double s0, double s1, double s2, double s3,
		double ain)
{
	mpfr_t t_mpfr, t2, t3, t4, t5, b, s, ain_mpfr;
    mpfr_t b0_mpfr, b1_mpfr, b2_mpfr, b3_mpfr, b4_mpfr, b5_mpfr;
    mpfr_t s0_mpfr, s1_mpfr, s2_mpfr, s3_mpfr;

	// Initialize variables with 200 bits of precision
	mpfr_init2(*rv, 200);
	mpfr_init2(t_mpfr, 200);
	mpfr_init2(t2, 200);
	mpfr_init2(t3, 200);
	mpfr_init2(t4, 200);
	mpfr_init2(t5, 200);
	mpfr_init2(b, 200);
	mpfr_init2(s, 200);
	mpfr_init2(ain_mpfr, 200);

   // Initialize coefficients
    mpfr_init2(b0_mpfr, 200);
    mpfr_init2(b1_mpfr, 200);
    mpfr_init2(b2_mpfr, 200);
    mpfr_init2(b3_mpfr, 200);
    mpfr_init2(b4_mpfr, 200);
    mpfr_init2(b5_mpfr, 200);
    mpfr_init2(s0_mpfr, 200);
    mpfr_init2(s1_mpfr, 200);
    mpfr_init2(s2_mpfr, 200);
    mpfr_init2(s3_mpfr, 200);

    // Convert double inputs to MPFR
    mpfr_set_d(t_mpfr, t, MPFR_RNDN);
    mpfr_set_d(ain_mpfr, ain, MPFR_RNDN);
    mpfr_set_d(b0_mpfr, b0, MPFR_RNDN);
    mpfr_set_d(b1_mpfr, b1, MPFR_RNDN);
    mpfr_set_d(b2_mpfr, b2, MPFR_RNDN);
    mpfr_set_d(b3_mpfr, b3, MPFR_RNDN);
    mpfr_set_d(b4_mpfr, b4, MPFR_RNDN);
    mpfr_set_d(b5_mpfr, b5, MPFR_RNDN);
    mpfr_set_d(s0_mpfr, s0, MPFR_RNDN);
    mpfr_set_d(s1_mpfr, s1, MPFR_RNDN);
    mpfr_set_d(s2_mpfr, s2, MPFR_RNDN);
    mpfr_set_d(s3_mpfr, s3, MPFR_RNDN);

	// Convert double inputs to MPFR
	mpfr_set_d(t_mpfr, t, MPFR_RNDN);
	mpfr_set_d(ain_mpfr, ain, MPFR_RNDN);

	// Calculate powers of t
	mpfr_mul(t2, t_mpfr, t_mpfr, MPFR_RNDN);      // t2 = t * t
	mpfr_mul(t3, t2, t_mpfr, MPFR_RNDN);          // t3 = t2 * t
	mpfr_mul(t4, t2, t2, MPFR_RNDN);              // t4 = t2 * t2
	mpfr_mul(t5, t3, t2, MPFR_RNDN);              // t5 = t3 * t2

	// Calculate b
	mpfr_set_d(b, b0, MPFR_RNDN);                  // b = b0
	mpfr_fma(b, b1_mpfr, t_mpfr, b, MPFR_RNDN);    // b += t*b1
	mpfr_fma(b, b2_mpfr, t2, b, MPFR_RNDN);   // b += t2*b2
	mpfr_fma(b, b3_mpfr, t3, b, MPFR_RNDN);   // b += t3*b3
	mpfr_fma(b, b4_mpfr, t4, b, MPFR_RNDN);   // b += t4*b4
	mpfr_fma(b, b5_mpfr, t5, b, MPFR_RNDN);   // b += t5*b5

	// Calculate s
	mpfr_set_d(s, s0, MPFR_RNDN);                  // s = s0
	mpfr_fma(s, s1_mpfr, t_mpfr, s, MPFR_RNDN);         // s += t*s1
	mpfr_fma(s, s2_mpfr, t2, s, MPFR_RNDN);             // s += t2*s2
	mpfr_fma(s, s3_mpfr, t3, s, MPFR_RNDN);             // s += t3*s3

	// Calculate result
	mpfr_sub(*rv, ain_mpfr, b, MPFR_RNDN);
	mpfr_div(*rv, *rv, s, MPFR_RNDN);            // rv = (ain - b) / s

	// Clear temporary variables
	mpfr_clear(t_mpfr);
	mpfr_clear(t2);
	mpfr_clear(t3);
	mpfr_clear(t4);
	mpfr_clear(t5);
	mpfr_clear(b);
	mpfr_clear(s);
	mpfr_clear(ain_mpfr);
	mpfr_clear(b0_mpfr);
	mpfr_clear(b1_mpfr);
	mpfr_clear(b2_mpfr);
	mpfr_clear(b3_mpfr);
	mpfr_clear(b4_mpfr);
	mpfr_clear(b5_mpfr);
	mpfr_clear(s0_mpfr);
	mpfr_clear(s1_mpfr);
	mpfr_clear(s2_mpfr);
	mpfr_clear(s3_mpfr);
	return 0;
}

int main(int argc, char *argv[])
{
	double orig, alt2, ite, alt7;
	mpfr_t m;
	if (argc != 1) {
		fprintf(stderr, "usage: %s < input.csv\n", argv[0]);
		return 1;
	}
	double     t,   b0,  b1,  b2,  b3,  b4,  b5,  s0,  s1,  s2,  s3,  ain;
	while (
	  scanf("%lf\t%lf\t%lf\t%lf\t%lf\t%lf\t%lf\t%lf\t%lf\t%lf\t%lf\t%lf\n",
	          &t,  &b0, &b1, &b2, &b3, &b4, &b5, &s0, &s1, &s2, &s3, &ain)
	  != EOF) {

		temp_mpfr(&m, t, b0, b1, b2, b3, b4, b5, s0, s1, s2, s3, ain);
		orig = temp(t, b0, b1, b2, b3, b4, b5, s0, s1, s2, s3, ain);
		alt2 = temp_alt2(t, b0, b1, b2, b3, b4, b5, s0, s1, s2, s3, ain);
		ite = temp_ite(t, b0, b1, b2, b3, b4, b5, s0, s1, s2, s3, ain);
		alt7 = temp_alt7(t, b0, b1, b2, b3, b4, b5, s0, s1, s2, s3, ain);

		// printf("mpfr\torig\talt2\tite\talt7\n");
		// 13 base-16 digits = 52 bits of precision in mantissa
		printf("%a\t%a\t%a\t%a\t%a\n", mpfr_get_d(m, MPFR_RNDN),orig,alt2,ite,alt7);
	}
	return 0;
}
