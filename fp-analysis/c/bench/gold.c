/* There's a lot going on, start with update_gain
 * Source: Implementation of https://www.kalmanfilter.net/default.aspx
 */
#include <stdio.h>

/* Update the current estimate uncertainty variance
 * requires \is_finite(p) && 0.0 < K <= 1.0;
 * ensures \result < p;
 */
double update_p(double K, double p)
{
  return (1.0 - K) * p;
}

/* K - Kalman gain
 * m - new measurement
 * x - existing state
 * requires 0 < K <= 1.0;
 */
double update_state(double K, double x, double m)
{
  return x + K * (m - x);
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

/* Start with a guess as current estimate
 * Read "sensor" (double from stdin) and incorporate it into the current estimate
 * Print the current estimate
 * Loop
 * There are four pieces of state:
 * + curr  - the current estimate
 * + p_var - the estimation variance. p_var is monotonically nonincreasing.
 * + r_var - assume the measurement variance is unchanged
 * + K     - the Kalman Gain.
 * assumes:
 *   1. scanf returns EOF after 10 iterations
 *   2. scanf sets the value of input to a valid double
 *      in the range [0.0, 2000.0], e.g. we assume the
 *      sensor will not malfunction (e.g. return NaN)
 */
int main() {
  double sensor_data[] = {1030.0, 989.0, 1017.0, 1009.0, 
    1013.0, 979.0, 1008.0, 1042.0, 1012.0, 1011.0};
  double input, K;
  double curr  = 990.0;  // Initial guess
  double p_var = 100.0;  // Estimation variance (10^2)
  double r_var = 225.0;  // Measurement variance (15^2
  int i;
//  printf("Weight\tp_var\tK\n");
//  while(scanf("%lf", &input) != EOF) {
    for(i = 0; i < 10; i ++) {
    input = sensor_data[i];
    K = update_gain(p_var, r_var);
    curr = update_state(K, curr, input);
    p_var = update_p(K, p_var);
//    printf("%8.3lf\t%8.3lf\t%8.3lf\n", curr, p_var, K);
  }
  return 0;
}
