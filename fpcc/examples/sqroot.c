/*@
  requires 0.0 <= x <= 1.0;
*/
double sqroot(double x)
{
    return (((1.0 + (0.5 * x)) - ((0.125 * x) * x)) + (((0.0625 * x) * x) * x))
    - ((((0.0390625 * x) * x) * x) * x);
}

int main(void)
{
    double result = sqroot(0.25);
    return 0;
}

