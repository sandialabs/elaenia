// Features we desire for Elaenia / FP error analysis, in order of approximate
// order of support.
// 1. Support for ACSL in fpcc via Language-C
// 2. Support for Vectors
// 3. Compositionality of specifications

// 2. Mapping from struct to vector
/*@
  predicate valid_vec3(vec3 x) =
   \valid(x.v+(0..2)) &&
   \is_finite(x.v[0]) &&
   \is_finite(x.v[1]) &&
   \is_finite(x.v[2]);

  predicate vec3_range(vec3 x, real lo, real hi) =
    valid_vec3(x) &&
	lo <= x.v[0] <= hi &&
	lo <= x.v[1] <= hi &&
	lo <= x.v[2] <= hi;
*/
typedef struct {
	float v[3];
} vec3;

float foo(vec3 *x)
{
	x->v[0] = 1.0/x->v[0];
	x->v[1] = 1.0/x->v[1];
	x->v[2] = 1.0/x->v[2];
}

float bar(vec3 *x)
{
	x->v[0] = 0.0;
	x->v[1] = x->v[1];
	x->v[2] = x->v[2];
}

float dot(vec3 x, vec3 y)
{
	return x.v[0] * y.v[0] +
	       x.v[1] * y.v[1] +
	       x.v[2] * y.v[2];
}

// 1. Support for ACSL in fpcc
// Begin with input ranges
// Later: uncertainty
/*@ requires \valid_vec3(x);
    requires vec3_range(x, 1e-5, 1.0);
    requires vec3_range(x, 0., 100.);
    // <<ensures to be filled out by PRECiSA>>
*/
// For Haskell Language-C: Use __attribute__ because comments get thrown out
// by preprocessor and C23 attribute syntax [[...]] isn't supported. I use
// warning now because I haven't figured out how to get any other syntax to
// compile.
// [[fpcc::requires("vec3_range(x, 1e-5, 1.);")]]
__attribute__((warning("requires vec3_range(x, 1e-5, 1.);")))
__attribute__((warning("requires vec3_range(y, 0., 100.);")))
float compose(vec3 x, vec3 y)
{
    foo(&x);
	bar(&y);
	// 3. Combine specs from foo and bar to get final theorem
	return dot(x,y);
}

int main(void)
{
	vec3 x, y;
	float res;
	res = compose(x, y);
	return 0;
}

