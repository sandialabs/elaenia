/* Trying to use the gappa backend for interval arithmetic */

/*@ requires 0.0 <= x && x <= 100.0;
  @ assigns \nothing;
  @ ensures \result <= 0.0 && \result <= 200.0;
*/
double twice(double x)
{
  return 2.0 * x;
}
