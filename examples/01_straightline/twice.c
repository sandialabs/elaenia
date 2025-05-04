/*@ requires \is_finite(x);
    requires 0.0 <= x && x <= 100.0;
    assigns \nothing;
    ensures finite: \is_finite(\result);
    ensures bound: \result <= 0.0 && \result <= 200.0;
*/
double twice(double x)
{
  return 2.0 * x;
}

int main(void)
{
    double result = twice(42.0);
    return 0;
}

