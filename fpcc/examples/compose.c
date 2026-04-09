
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

float compose(vec3 x, vec3 y)
{
	// 1. Inline foo and bar
	// foo(&x);
	// bar(&y);
	x->v[0] = 1.0/x->v[0];
	x->v[1] = 1.0/x->v[1];
	x->v[2] = 1.0/x->v[2];

	y->v[0] = 0.0;
	y->v[1] = y->v[1];
	y->v[2] = y->v[2];

	// 2. Combine specs from foo and bar to get final theorem
	return dot(x,y);
}

