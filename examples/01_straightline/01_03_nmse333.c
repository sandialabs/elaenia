// NMSE problem 3.3.3 
// Precondition x != 0, 1, or -1
// Source: FPBench hamming-1987

double nmse(double x) {
	return ((1.0 / (x + 1.0)) - (2.0 / x)) + (1.0 / (x - 1.0));
}
