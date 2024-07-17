/*
  To run: ./gps
  sensor data generated with the following R script:
```
  n <- 14
  v <- 3 # Constant velocity model
  x <- rep(20.0, n)
  dt <- 1
  q <- rnorm(n, 0, 1) # Process noise
  for(i in seq(2,n)) {
    x[i] <- x[i-1] + v + q[i] # No acceleration
  }
  m <- x + rnorm(n, 0, 4) # Sensor noise
  t <- seq(0, by=dt, length.out=n)
```
*/
#include "Matrix_Algebra.h"

#include <stdio.h>

#ifndef VERBOSE
#define VERBOSE 1
#endif

/*@ requires dt >= 0.0;
 */
int build_Q(Matrix_3x3 *Q, double dt)
{
	Q->s._11 = 0.25 * dt * dt * dt * dt; Q->s._12 = 0.5 * dt * dt * dt; Q->s._13 = 0.5 * dt * dt;
	Q->s._21 = 0.50 * dt * dt * dt     ; Q->s._22 = dt * dt           ; Q->s._23 = dt;
	Q->s._31 = 0.50 * dt * dt          ; Q->s._32 = dt                ; Q->s._33 = 1.;
	return 0;
}

int build_P(Matrix_3x3 *P)
{
	P->s._11 = 25.; P->s._12 = 0.;  P->s._13 = 0.;
	P->s._21 = 0.;  P->s._22 = 10.; P->s._23 = 0.;
	P->s._31 = 0.;  P->s._32 = 0.;  P->s._33 = 1.;
	return 0;
}

/*@ requires dt >= 0.0;
 */
int build_F(Matrix_3x3 *F, double dt)
{
	F->s._11 = 1.; F->s._12 = dt; F->s._13 = 0.5 * dt * dt;
	F->s._21 = 0.; F->s._22 = 1.; F->s._23 = dt;
	F->s._31 = 0.; F->s._32 = 0.; F->s._33 = 1.;
	return 0;
}

/* Predict and update uncertainty covariance P
 * P_{n}   = F * P_{n-1} * F^T
 * P_{n|n} = 
 */
int predict_P(Matrix_3x3 *P, const Matrix_3x3 *F, const Matrix_3x3 *Q)
{
	axbT_33(P, F, P);
	axb_33(F, P, P);
    a_add_b_33(P, Q, P);
	return 0;
}

int predict_x(Vector_3 *x, double dt)
{
	x->ijk[0] = x->ijk[0] + x->ijk[1] + 0.5*dt*dt*x->ijk[2];
	x->ijk[1] = x->ijk[1] + x->ijk[2];
	// x->ijk[2] = x->ijk[2];
	return 0;
}

int update_P(Matrix_3x3 *P, const Vector_3 *K)
{
	Matrix_3x3 eyekh;
	eyekh.s._11 = 1. - K->ijk[0]; eyekh.s._12 = 0.; eyekh.s._13 = 0.;
	eyekh.s._21 =    - K->ijk[1]; eyekh.s._22 = 1.; eyekh.s._23 = 0.;
	eyekh.s._31 =    - K->ijk[2]; eyekh.s._32 = 0.; eyekh.s._33 = 1.;
	axb_33(&eyekh, P, P);
	return 0;
}


int update_K(Vector_3 *K, const Matrix_3x3 *P, double r)
{
	K->ijk[0] = P->s._11 / (P->s._11 + r);
	K->ijk[1] = P->s._21 / (P->s._11 + r);
	K->ijk[2] = P->s._31 / (P->s._11 + r);
	return 0;
}

int update_x(Vector_3 *x, const Vector_3 *K, double y)
{
	x->ijk[0] = x->ijk[0] + K->ijk[0] * y;
	x->ijk[1] = x->ijk[1] + K->ijk[1] * y;
	x->ijk[2] = x->ijk[2] + K->ijk[2] * y;
	return 0;
}

void print_header()
{
	if (VERBOSE) {
		printf("n\trow\tK\tx\tP(:,1)\tP(:,2)\tP(:,3)\n");
	} else {
		printf("n\trow\tK\tx\n");
	}
}

void print_results(Matrix_3x3 *P, Vector_3 *K, Vector_3 *x, int n)
{
	int i = 0;
	for (i = 0; i < 3; i++) {
		printf("%d\t%d\t%.4f\t%.4f",
			n, i+1, K->ijk[i], x->ijk[i]);
		if (VERBOSE) {
			printf("\t%.4f\t%.4f\t%.4f",
				P->a[i][0], P->a[i][1], P->a[i][2]);
		}
		printf("\n");
	}
}

/*
int print1(const char * p) {
  return printf("%s", p);
}
*/

/*
int print3(double f1, double f2, double f3) {
  return printf("%8.3lf\t%8.3lf\t%8.3lf\n", f1, f2, f3);
}
int scan(double * p) {
  return scanf("%lf", p);
}
*/

/* Start with a guess as current estimate
 * Read "sensor" (double from stdin) and incorporate it into current estimate
 * m is the current measurement.
 * Print the current estimate, variance, and Kalman gain each iteration
 * Loop
 * There are five pieces of state:
 * + temp  - the current estimate
 * + rate  - current rate of change
 * + p_var - the estimation variance. p_var is monotonically nonincreasing.
 * + r_var - assume the measurement variance is unchanged
 * + K     - the Kalman Gain.
 * + q     - the process noise variance for measurement; distributed N(0,q)
 * assumes:
 *   1. scanf returns EOF after 14 iterations
 *   2. scanf sets the value of input to a valid double
 *      in the range [0.0, 200.0], e.g. we assume the
 *      sensor will not malfunction (e.g. return NaN)
 */
int main()
{
	int n = 14;
	int i;
	double sensor_data[] = {
	  10.32053, 17.34839, 31.04178, 34.21409, 36.34723, 29.81774, 28.00129, 41.06721, 37.83178, 42.29896, 55.64220, 50.47855, 52.23186, 60.42627};
	Vector_3 K, x;
	Matrix_3x3 F, P, Q;
	double y;                 // residual
	double m;                 // Measurement (z = [m])
	double dt        =    1.; // Time between measurements
	x.ijk[0]         =   20.; // Initial guess
	x.ijk[1]         =    0.;
	x.ijk[2]         =    0.;
	double r         =   16.; // Measurement variance (4^2)
    build_Q(&Q, dt);
	build_P(&P);
	build_F(&F, dt);
//  print1("x\tp_var\tK\n");
//  while(scan(&m) != EOF) {
	print_header();
	for(i = 0; i < n; i ++) {
		m = sensor_data[i];
		predict_x(&x, dt);
		predict_P(&P, &F, &Q);
		y = m - x.ijk[0];
		update_K(&K, &P, r);
		update_x(&x, &K, y);
		update_P(&P, &K);
		print_results(&P, &K, &x, i);
	}
	return 0;
}
