double foo(double x)
{
    double z;
    if (x < 6.5) {
        z = x * 3.6;
    } else {
        z = x - 8.76;
    }
    return z;
}

int main() {
    foo(100);
}
