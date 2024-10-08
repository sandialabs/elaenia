// Source: FPBench, darulova-kuncak-2014
// 4th order taylor series approximation for square root
// :pre (<= 0 x 1)
double sqroot(double x) {
    return (((1.0 + (0.5 * x)) - ((0.125 * x) * x)) + (((0.0625 * x) * x) * x))
    - ((((0.0390625 * x) * x) * x) * x);
}

