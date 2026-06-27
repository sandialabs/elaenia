// |real - floating-point| <= 0.00000000000020853586331318513
/*@
  requires -100 <= u <= 100;
  requires 20 <= v <= 20000;
  requires -30 <= T <= 50;
*/
double doppler1(double u, double v, double T) {
	double t1 = 331.4 + (0.6 * T);
	double r = (-t1 * v) / ((t1 + u) * (t1 + u));
	return r;
}

// |real - floating-point| <= 0.0000000000003215205879314454
/*@
  requires -15 <= x1 <= 15;
  requires -15 <= x2 <= 15;
  requires -15 <= x3 <= 15;
*/
double rigidBody1(double x1, double x2, double x3) {
	double r = (((-(x1 * x2)) - ((2.0 * x2) * x3)) - x1) - x3;
	return r;
}

// |real - floating-point| <= 0.000000000036465941377628055
/*@
  requires -15 <= x1 <= 15;
  requires -15 <= x2 <= 15;
  requires -15 <= x3 <= 15;
*/
double rigidBody2(double x1, double x2, double x3) {
	double r = ((((((2.0 * x1) * x2) * x3) + ((3.0 * x3) * x3)) - (((x2 * x1) * x2) * x3)) + ((3.0 * x3) * x3)) - x2;
	return r;
}

// |real - floating-point| <= 0.000000000023580063834600673
/*@
  requires -5 <= x1 <= 5;
  requires -20 <= x2 <= 5;
*/
double jetEngine(double x1, double x2) {
	double t =     (((3.0 * x1) * x1) + (2.0 * x2)) - x1;
	double t_42_ = (((3.0 * x1) * x1) - (2.0 * x2)) - x1;
	double d = (x1 * x1) + 1.0;
	double s = t / d;
	double s_42_ = t_42_ / d;

	double r =  x1 + (((((((((2.0 * x1) * s) * (s - 3.0)) + ((x1 * x1) * ((4.0 * s)
	- 6.0))) * d) + (((3.0 * x1) * x1) * s)) + ((x1 * x1) * x1)) + x1) + (3.0 *
	s_42_));

	return r;
}

// |real - floating-point| <= 0.00000000000002657069511407688
/*@
  requires -4.5 <= v <= -0.3;
  requires 0.4 <= w <= 0.9;
  requires 3.8 <= r <= 7.8;
*/
double turbine1(double v, double w, double r) {
	double ret = ((3.0 + (2.0 / (r * r))) - (((0.125 * (3.0 - (2.0 * v))) * (((w * w)
	* r) * r)) / (1.0 - v))) - 4.5;

	return ret;
}

// |real - floating-point| <= 0.000000000000031233064051920534
/*@
  requires -4.5 <= v <= -0.3;
  requires 0.4 <= w <= 0.9;
  requires 3.8 <= r <= 7.8;
*/
double turbine2(double v, double w, double r) {
	double ret = ((6.0 * v) - (((0.5 * v) * (((w * w) * r) * r)) / (1.0 - v))) - 2.5;
	return ret;
}

// |real - floating-point| <= 0.00000000000001841023435689368
/*@
  requires -4.5 <= v <= -0.3;
  requires 0.4 <= w <= 0.9;
  requires 3.8 <= r <= 7.8;
*/
double turbine3(double v, double w, double r) {
	double ret = ((3.0 - (2.0 / (r * r))) - (((0.125 * (1.0 + (2.0 * v))) * (((w * w) * r) * r)) / (1.0 - v))) - 0.5;
	return ret;
}

// |real - floating-point| <= 0.0000000000000005137805199232649
/*@
  requires 0.1 <= x <= 0.3;
*/
double verhulst(double x) {
	double r = 4.0;
	double K = 1.11;
	double ret = (r * x) / (1.0 + (x / K));
	return ret;
}

// |real - floating-point| <= 0.0000000000000002144476123635858
/*@
  requires 0.1 <= x <= 0.3;
*/
double predatorPrey(double x) {
	double r = 4.0;
	double K = 1.11;
	double ret = ((r * x) * x) / (1.0 + ((x / K) * (x / K)));
	return ret;
}

// |real - floating-point| <= 0.00000000710412085493166
/*@
  requires 0.1 <= v <= 0.5;
*/
double carbonGas(double v) {
	double p = 35000000.0;
	double a = 0.401;
	double b = 4.27e-5;
	double t = 300.0;
	double n = 1000.0;
	double k = 1.3806503e-23;
	double ret = ((p + ((a * (n / v)) * (n / v))) * (v - (n * b))) - ((k * n) * t);
	return ret;
}

// |real - floating-point| <= 0.0000000000000006834810495348622
/*@
  requires 0 <= x <= 1;
*/
double sqroot(double x) {
	double ret = (((1.0 + (0.5 * x)) - ((0.125 * x) * x)) + (((0.0625 * x) * x) * x))
	- ((((0.0390625 * x) * x) * x) * x);

	return ret;
}

// |real - floating-point| <= 0.0000000000000012290285263299633
/*@
  requires -2 < x < 2;
*/
double sineOrder3(double x) {
	double ret = (0.954929658551372 * x) - (0.12900613773279798 * ((x * x) * x));
	return ret;
}

// TODO:
// Conditionals are not current supported in fpcc. In
// src/Intermediate/Linter.hs, `condLinter` rejects any `if`s in the program.
//
// // :pre (< 0 x 10)
// double cav10(double x) {
// 	double tmp;
// 	if (((x * x) - x) >= 0.0) {
// 		tmp = x / 10.0;
// 	} else {
// 		tmp = (x * x) + 2.0;
// 	}
// 	return tmp;
// }

// |real - floating-point| <= 0.00000000000000010639637319324422
/*@
  requires 0 <= u <= 1;
*/
double bspline3(double u) {
	double ret = (-((u * u) * u)) / 6.0;
	return ret;
}
