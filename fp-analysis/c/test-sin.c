// From  FPbench (https://fpbench.org/benchmarks.html#sine)
// -pi/2 < x < pi/2
double sin_dbl(double x)
{
    double y = 
        x - (x * x * x) / 6.0 + (x * x * x * x * x) / 120.0 - 
        (x * x * x * x * x * x * x) / 5040.0;
        /*
    double y = 
        ((x - (((x * x) * x) / 6.0)) + ((((((x * x) * x) * x) * x) / 120.0)));
        */
    return y;
}

int main()
{
    sin_dbl(0);
}
