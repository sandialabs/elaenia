/* 7th order taylor series approximation for sine at 0
 * precondition: -pi/2 < x < pi/2
 * source: FPBench
 */
double sin_dbl(double x)
{
    double y = 
        ((x - (((x * x) * x) / 6)) + ((((((x * x) * x) * x) * x) / 120))) - 
        (((((((x * x) * x) * x) * x) * x) * x) / 5040);
    return y;
}

