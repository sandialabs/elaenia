// Second-order taylor series approximation of sqrt(1 + x)
/*@
  requires 0.0 <= x <= 1.0;
  requires \is_finite(x);
  ensures result: 1.0 <= \result <= 1.375;
  // ensures real: \abs(\result - (double)(\sqrt(1+x))) < 0.5;
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

