// Source: FPBench, darulova-kuncak-2014
// Testing with attr syntax (both [[...]] from C23 and __attribute__ from GNU extension)
/*@
  requires 0.0 <= x <= 1.0;
  requires \is_finite(x);
  ensures 1 <= \result <= 1.40;
  assigns \nothing;
 */
__attribute__(requires 0.0 <= x <= 1.0;)
__attribute__(requires \is_finite(x);)
__attribute__(ensures 1 <= \result <= 1.40;)
__attribute__(assigns \nothing;)
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

