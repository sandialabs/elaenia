#include <limits.h>

typedef struct Vector {
  int n;
  float *v;
} Vector;


/*@
  predicate read1d(integer n, float *a) =
    0 <= n && \valid_read(a+(0..(n-1)));
  
  predicate valid_read_Vector(Vector A) = read1d(A.n, A.v);
*/

/*@ requires valid_read_Vector(x);
  @ requires valid_read_Vector(y);
  @ requires x.n == y.n;
  @ assigns \nothing;
 */
float dot(Vector x, Vector y) {
	double acc = 0.0;
	/*@ loop invariant 0 <= i <= x.n;
	  @ loop assigns acc;
	  @ loop assigns i;
	  @ loop variant x.n-i;
	*/
	for (int i = 0; i < x.n; i++) {
		acc += x.v[i] * y.v[i];
	}
	return acc;
}

/*@ requires valid_read_Vector(x);
  @ requires valid_read_Vector(y);
  @ requires x.n == y.n;
  @ assigns \nothing;
 */
float dot_unroll(Vector x, Vector y) {
	int i;
	double acc = 0.0;
	/*@ loop invariant 0 <= i <= x.n;
	  @ loop assigns acc;
	  @ loop assigns i;
	  @ loop variant x.n-i;
	*/
	for (i = 0; i < x.n-4; i += 4) {
		acc += x.v[i+0] * y.v[i+0];
		acc += x.v[i+1] * y.v[i+1];
		acc += x.v[i+2] * y.v[i+2];
		acc += x.v[i+3] * y.v[i+3];
	}
	// Fill out the non-multiples of 4
	for (; i < x.n; i++) {
		acc += x.v[i] * y.v[i];
	}
	return acc;
}

// Different associativity
/*@ requires valid_read_Vector(x);
  @ requires valid_read_Vector(y);
  @ requires x.n == y.n;
  @ assigns \nothing;
 */
float dot_reassociate(Vector x, Vector y) {
	int i;
	double acc = 0.0;
	/*@ loop invariant 0 <= i <= x.n;
	  @ loop assigns acc;
	  @ loop assigns i;
	  @ loop variant x.n-i;
	*/
	for (i = 0; i < x.n-4; i += 4) {
		acc += ((x.v[i+0] * y.v[i+0]) +
                 x.v[i+1] * y.v[i+1]) +
		        (x.v[i+2] * y.v[i+2] +
		         x.v[i+3] * y.v[i+3]);
	}
	// Fill out the non-multiples of 4
	for (; i < x.n; i++) {
		acc += x.v[i] * y.v[i];
	}
	return acc;
}


/*@ assigns \nothing;
 */
int dot_frama_c_check()
{
	int X[4] = {0, 1, 2, 3};
	int Y[4] = {0, 1, 2, 3};
	int acc = 0;
	int i;
	/*@ loop invariant 0 <= i <= 4;
	  @ loop assigns acc;
	  @ loop assigns i;
	  @ loop variant 4-i;
	*/
	// [wp] [Timeout] typed_real_dot2_loop_assigns_part2 (Qed 4ms) (Alt-Ergo)
	for (i = 0; i < 4; i++) {
		acc += X[i] * Y[i];
	}
	return acc;
}


int main() {
	float xv[4] =  {-1.0, 0.0, 1.0, 2.0};
	float yv[4] =  {-1.0, 0.0, 1.0, 2.0};
	Vector x = {.n = 4, .v = xv};
    Vector y = {.n = 4, .v = yv};
	dot(x,y);
}
