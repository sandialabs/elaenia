// Source: FPBench darulova-kuncak-2014
// requires (and (<= -100 u 100) (<= 20 v 20000) (<= -30 T 50))
// ensures error < 1e-12
double doppler1(double u, double v, double T) {
	double t1 = 331.4 + (0.6 * T);
	return (-t1 * v) / ((t1 + u) * (t1 + u));
}

