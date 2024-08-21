
/*@ requires 0.0 <= x <= 1000.0;
  @ requires 0.1 <= y <= 10.0;
  @ assigns \nothing;
  @ ensures 0.0 <= \result <= 10000.0;
 */
double div(float x, float y)
{
	return x / y;
}
