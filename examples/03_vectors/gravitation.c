/* Computes the gravitational acceleration vector at a specified ECEF location
 * using the JGM2 gravitational ellipsoid only. Higher-order gravity terms (the
 * "gravity anomaly") are ignored. Only the pure ellipsoid is used.
 * Source: 
 * https://www.mathworks.com/matlabcentral/fileexchange/8359-ellipsoidal-gravity-vector/files/xyz2grav.m
 * ECEF Coordinates from
 * https://dominoc925-pages.appspot.com/mapplets/cs_ecef.html
 */
#include <math.h>
#include <stdio.h>

typedef struct {
	double i, j, k;
} Vec3;


/* Verification questions we may want to ask: (these are not complete) */
/* logic real norm3(Vec3 a) = sqrt(a.i*a.i + a.j*a.j + a.k*a.k); */
/* requires \valid_read(a);
   requires ??? <= norm3(a) <= ???;
   assigns \nothing;
   ensures \is_finite(\result);
   ensures \result >= 0.0
 */
double norm_3(const Vec3* a) {
	return sqrt(a->i*a->i + a->j*a->j + a->k*a->k);
}

/* Verification questions we may want to ask: */
/* requires \valid_read(r_e);
 * requires \valid(g_e);
 * requires ??? <= norm3(r_e) <= ???;
 * assigns g_e;
 */
void gravitation_ecef(Vec3* r_e, Vec3* g_e)
{
	/* WGS84_EARTH_MU, Earth gravitational constant from WGS84 model: 3.986004418e14 m³/s². */
	double MU = 3.986004418e14;
	/* WGS84_EARTH_EQUATORIAL_RADIUS, Earth equatorial radius from WGS84 model: 6378137.0 m. */
	double R = 6378137.;

	/* Earth oblateness gravity coefficient (non-dimensional) */
	double J2 = 0.00108263;

	/* Euclidean distance from origin ([0,0,0] for ECEF) */
	double r = norm_3(r_e);
	double sub1 = 1.5*J2*(R/r) * (R/r);
	double sub2 = 5*r_e->k * r_e->k /(r*r);
	double sub3 = -MU/(r*r*r);
	double sub4 = sub3*(1 - sub1*(sub2 - 1.));
	g_e->i = r_e->i*sub4; 
	g_e->j = r_e->j*sub4; 
	g_e->k = r_e->k*sub3*(1. - sub1*(sub2 - 3.));
}

int main(int argc, char *argv[])
{
	// ECEF for University of California, Berkeley Campanile
	Vec3 r = { -2690634., -4263092., 3894249. };
	Vec3 g;
	gravitation_ecef(&r, &g);
	printf("(%e,%e,%e)\n", g.i, g.j, g.k);
}

