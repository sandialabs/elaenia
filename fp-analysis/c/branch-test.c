// From Solovyev et al. FPTaylor
// 0 <= a <= 100
// 0 <= b <= 100
int foo(double a, double b) {
    double r;
    if (b >= a) {
        r = b / (b - a + 0.5);
    } else {
        r =  b / 0.5;
    }
    return 0;
}

int main() {
}
