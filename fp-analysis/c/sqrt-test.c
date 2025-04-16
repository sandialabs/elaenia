/*
(-
 (+ (- (+ 1 (* 1/2 x)) (* (* 1/8 x) x)) (* (* (* 1/16 x) x) x))
  (* (* (* (* 5/128 x) x) x) x))
*/

double sqroot(double x) {
    double y;
    y = ((((1.0 / 2.0) * x + 1) - ((1.0 / 8.0) * x * x)) + (x * x * x * (1.0 / 16.0))) - 
        ((5.0 / 128.0) * x * x * x * x);
    return y;
}

int main() {
    foo(2.0);
}
