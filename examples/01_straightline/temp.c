/*@
  requires -35.    <= t <= 80.;
  requires -1.     <= b0 <= 1.;
  requires -1e-4   <= b1 <= 1.e-4;
  requires -1e-6   <= b2 <= 1.e-6;
  requires -1e-9   <= b3 <= 1.e-9;
  requires -1e-12  <= b4 <= 1.e-12;
  requires -1e-13  <= b5 <= 1.e-13;
  requires \is_finite(b0) && \is_finite(b1) && \is_finite(b2) && \is_finite(b3) && \is_finite(b4) && \is_finite(b5);
  requires -0.9    <= s0 <= 1.1;
  requires -1e-4   <= s1 <= 1.e-4;
  requires -1e-6   <= s2 <= 1.e-6;
  requires -1e-9   <= s3 <= 1.e-9;
  requires \is_finite(s0) && \is_finite(s1) && \is_finite(s2) && \is_finite(s3);
  requires -256.   <= ain <= 256.;
  requires \is_finite(ain);
  assigns \nothing;
*/
// Thought: axiom bound implies is_finite
double temp(double t,
		double b0, double b1, double b2, double b3, double b4, double b5,
		double s0, double s1, double s2, double s3,
		double ain)
{
	double t2 = t*t;
	double t3 = t2*t;
	double t4 = t2*t2;
	double t5 = t3*t2;

// Failed goal: Prove: is_finite_f64(add_f64(a_3, a_1)).
// Let a = mul_f64(t, t).
// Let a_1 = mul_f64(a, b2_0).
// Let a_2 = mul_f64(t, b1_0).
// Let a_3 = add_f64(b0_0, a_2).
//	double t4trm = t2*b2 + b0*

	double b = b0 + t*b1 + t2*b2 + t3*b3 + t4*b4 + t5*b5;
	double s = s0 + t*s1 + t2*s2 + t3*s3;
	return (ain - b)/s;
}

int main(void) {
	double result = temp(20.0,
	                     0.5, 5e-5, 5e-7, 5e-10, 5e-13, 5e-14,
	                     1.05, 5e-5, 5e-7, 5e-10,
	                     128.0);
	return 0;
}
