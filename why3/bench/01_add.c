/*@ requires 1.0 <= x <= 10.0;
  @ requires 1.0 <= y <= 10.0;
  @ assigns \nothing;
  @ ensures 2.0 <= \result <= 20.0;
 */
float add(float x, float y)
{
	return x + y;
}

