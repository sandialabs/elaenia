/*
  To run: ./kettle < sensor_data
  sensor data generated with the following R commands:
  n <- 14
  x <- rep(20.0, n) + rnorm(n, 0, 1)
  x[(n/2):n] <- x[(n/2):n] + 2*seq(n/2+1)
*/
#include <stdio.h>

/* Update the current estimate uncertainty variance.
 * In reality, P is a covariance matrix. However, since this model is
 * simplified to a two-dimensional case and we assume independence of
 * the measurements, we only compute
 * [ p,  0    ;
 *   0,  p_del]
 * For a more complete derivation, see kettle.pdf
 * K - Kalman Gain
 * p - old estimation variance
 * q - process variance
 */
/*@
 * \requires \is_finite(p) && \is_finite(q) &&
 *   \is_finite(t) && \is_finite(K) && \is_finite(p_del);
 * \requires 0.0 <= p;   // Note: We may want to clamp p, q, t, p_del
 * \requires 0.0 <= q;   // to reasonable values to get error bounds. For
 * \requires 0.0 <= t;   // example: t <= 10, q <= 100, p <= 1e4, p_del <= 1e4
 * \requires 0.0 <= p_del;
 * \requires 0.0 < K <= 1.0;
 * \ensures 0.0 <= \result <= ???;
 */
double update_p(double K, double p, double p_del, double t, double q)
{
  return (1.0 - K) * p + t*t*p_del + q;
}

/* K - Kalman gain
 * m - new measurement
 * x - existing state
 * requires 0 < K <= 1.0;
 */
double update_state(double K, double x, double x_del, double t, double m)
{
  //     update          predict
  return x + t * x_del + K * (m - x);
}

/* Update the current estimate's derivative uncertainty variance
 */
double update_p_del(double p_del, double q)
{
  return p_del + q;
}

/* Update the kalman gain. */
/* requires \is_finite(p) && is_finite(r) &&
 *          p > 0.0 && r > 0.0
 * some other bounds on p, r
 * ensures 0.0 <= \result <= 1.0
 */
/* If we decide to go the route of full floating-point error: There are some
 * small positive numbers x such that 1/x == Inf. We may assume p and r are
 * greater than those.
 */
double update_gain(double p, double r)
{
  return p / (p + r);
}
/*
int print1(const char * p) {
  return printf("%s", p);
}

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
int main() {
  double sensor_data[] = {19.70, 20.35, 20.09, 21.04,
	  17.79, 21.01, 22.25, 22.91, 25.54, 29.61,
	  30.38, 30.28, 33.73, 35.71};
  double m, K;
  double t         =   5.0; // Time between measurements
  double temp      =  16.0; // Initial guess temperature
  double rate      =   0.0; // Initial guess heating rate
  double p_var     = 100.0; // Estimation variance (10^2)
  double p_del_var =   0.0; // Estimation variance
  double r_var     =  16.0; // Measurement variance (4^2)
  double q         =   1.0; // Process variance noise (1^2)
  int i;
  // TODO: Model as matrix
//  print1("temperature\tp_var\tK\n");
//  while(scan(&m) != EOF) {
    for(i = 0; i < 14; i ++) {
    m          = sensor_data[i];
    K          = update_gain(p_var, r_var);
    temp       = update_state(K, m, rate, t, m);
    rate       = rate; // Constant heating rate
    p_var      = update_p(K, p_var, p_del_var, t, q);
    p_del_var  = update_p_del(p_del_var, 0.0);
//    print3(temp, p_var, K);
  }
  return 0;
}
