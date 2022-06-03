
/*@ requires 0.0 <= x && x <= 1000.0;
 */
double add(double x)
{
  return x + 0.2;
}

int main(int argc, char *argv[])
{
	double x;
  x = add(0.1);
	return 0;
}
