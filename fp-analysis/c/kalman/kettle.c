/*
  Code inspired by Chapter 4 and 14 of
    https://github.com/rlabbe/Kalman-and-Bayesian-Filters-in-Python
  Usage: make && ./kettle
  The sensor data represents an electric kettle that is switched on at t=8.
  Sensor data generated with the following R commands:
  n <- 14
  x <- rep(20.0, n) + rnorm(n, 0, 1)
  x[(n/2):n] <- x[(n/2):n] + 10*seq(n/2+1)
*/
#include <stdio.h>


/* We inline all the following functions to make analysis possible
 * with our abstract interpretation approach.
 */
/* Update the current estimate uncertainty variance
 * K - Kalman Gain
 * p - old estimation variance
 * q - process variance
 * \requires \is_finite(p) && 0.0 <= q && t < 0.0 && 0.0 < K <= 1.0;
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

/* Start with a guess as current estimate */
int main() {
  double sensor_data[] = {
    20.79148, 20.09775, 19.42749, 19.60912, 19.37787, 21.47362, 30.42308,
    38.58739, 50.17102, 58.30209, 69.96654, 79.27626, 90.44830, 101.32235};
        double m;            // Measurement
        double y;            // Residual of estimation
        double K;            // Kalman Gain
        double t     =  5.0; // Time between measurements
        double temp  = 18.0; // Initial guess temperature
  const double rate  =  0.2; // Initial guess heating rate
        double p_var = 25.0; // Temp estimation variance
  const double r_var =  1.0; // Measurement noise variance
  const double q_s   = 0.25; // Process noise variance, stable
  const double q_h   =  5.0; // Process noise variance, heating
        double q     =  q_s; // Measurement noise variance
        int i;
  //printf("m\ttemp\tp_var\tK\n");
  for(i = 0; i < 14; i ++) {
    m          = sensor_data[i];
    // Update
    y          = m - temp;
    K          = p_var / (p_var + r_var); // S simplifies to (p + r)
    temp       = temp + K * y;
    p_var      = (1.0 - K) * p_var;
    // Predict
    temp       = temp + t * rate;
    p_var      = p_var + q;
    // Adapt
    if (y * y > 5.0 * (p_var + r_var)) { // uncertainty exceeds 5 std deviations
      q = q_h;
    } else {
      q = q_s;
    }
    //printf("%8.3lf\t%8.3lf\t%8.3lf\t%8.3lf\n", m, temp, p_var, K);
  }
}
