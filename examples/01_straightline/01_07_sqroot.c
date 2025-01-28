// Source: FPBench, darulova-kuncak-2014
// 4th order taylor series approximation for square root
// :pre (<= 0 x 1)
// Results from Gappa:
// e in [43b-7 {0.335938, 2^(-1.57374)}, 17b-4 {1.0625, 2^(0.0874628)}]
/*@
  requires 0.0 <= x <= 1.0;
  requires \is_finite(x);
  //ensures 0.0 <= \result <= 1.0625;
  //ensures -1.0 <= \result <= 2.0;
  ensures 0.335938 <= \results <= 1.0625;
  assigns \nothing;
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

