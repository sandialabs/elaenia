/*
 * To run: ./flow < sensor_data
 */
#include <stdio.h>

#define ALPHA 0.5
#define BETA  0.25

/* x     - the current weight estimate
 * m     - the new measurement to incorporate
 * alpha - Weight of measurement vs current estimation
 */
double update_state(double x, double m, double alpha)
{
  return x + alpha * (m - x);
}

/* f     - the current flow estimate
 * x     - the current weight estimate
 * m     - the new measurement to incorporate
 * delta - time elapsed between measurements
 * beta  - Weight of measurement vs current estimation
 */
double update_flow(double f, double x, double m, double delta, double beta)
{
  return f + beta * ((m - x) / delta);
}

/* f     - the current flow estimate
 * x     - the current weight estimate
 * delta - time elapsed between measurements
 */
double extrapolate(double f, double x, double delta)
{
	return x + f * delta;
}

/* We essentially make an alpha-beta filter here
 * where we pick some ALPHA and BETA;
 * alpha = 1 means you only use measurement for weight,
 * alpha = 0 means you only use existing model
 * beta = 1 means you adjust the flow rate completely according to measurement
 * beta = 0 means you do not adjust flow rate according to measurement
 */

/*
  Start with a guess as current estimate
  Read "sensor" (double from stdin) and incorporate it into the current estimate
  Print the current estimate
  Loop
  There are two pieces of state:
  + curr - the current estimate of weight
  + flow - the current estimate of flow rate
*/
int main(int argc, char *argv[])
{
  double curr = 1000.0; // initial guess of weight
  double flow = 5.0;    // initial guess of flow rate
  double delta = 2.0;   // time between measurements
  double input;
  while(scanf("%lf", &input) != EOF) {
    flow = update_flow(flow, curr, input, delta, BETA);
    curr = update_state(curr, input, ALPHA);
    curr = extrapolate(flow, curr, delta);
    printf("%8.3lf\n", curr);
  }
  return 0;
}

