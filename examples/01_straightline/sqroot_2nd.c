// Second-order taylor series approximation of sqrt(x)
/*@
  requires 0.0 <= x <= 1.0;
  requires \is_finite(x);
  //ensures 0.0 <= \result <= 1.0625;
  //ensures -1.0 <= \result <= 2.0;
  ensures result: 0.0 <= \result <= 1.5;
  assigns \nothing;
 */
double sqroot_2nd(double x)
{
    return (1.0 + (0.5 * x)) - ((0.125 * x) * x);
}

int main(void)
{
    double result = sqroot_2nd(0.25);
    return 0;
}

