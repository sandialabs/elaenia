#include <stdio.h>
#include <stdlib.h>
#include "Matrix_Algebra.h"

#define PN 5

/* Fills a matrix with uniform(-1,1) */
int fill_matrix(Matrix_MxN *a, int M, int N)
{
	int i, j;
	if (M > MAX_N || N > MAX_N) {
		fprintf(stderr, "error: M or N > MAX_N\n");
		return 1;
	}
	a->m = M;
	a->n = N;
	for (i = 0; i < M; i++) {
		for (j = 0; j < N; j++) {
			a->a[i][j] = (double) rand() / RAND_MAX * 2.0 - 1.0;
		}
	}
	return 0;
}

/* Checks for bitwiwse equality */
int matrix_equal(Matrix_MxN *a, Matrix_MxN *b, int M, int N)
{
	int i, j;
	if (M > MAX_N || N > MAX_N) {
		return 0;
	}
	for (i = 0; i < M; i++) {
		for (j = 0; j < N; j++) {
			if (a->a[i][j] != b->a[i][j]) {
				printf("at (%d,%d) %a != %a\n",
				       i, j, a->a[i][j], b->a[i][j]);
				return 0;
			}
		}
	}
	return 1;
}

void print_matrix(Matrix_MxN *a, const char* msg, int M, int N)
{
	int i, j;
	printf("%s = [\n", msg);
	if (M > MAX_N || N > MAX_N) {
		fprintf(stderr, "Bad dimensions\n");
	}
	for (i = 0; i < M; i++) {
		printf("  ");
		for (j = 0; j < N; j++) {
			if (i == M-1 && j == N-1) {
				printf("%.3f]", a->a[i][j]);
			} else {
				printf("%.3f, ", a->a[i][j]);
			}
		}
		printf("\n");
	}
}

int main(int argc, char *argv[])
{
	int i, j;
	int M = PN;
	int N = PN;

	Matrix_MxN a;
	Matrix_MxN ai;
	Matrix_MxN eye;
	Matrix_MxN aai;
	ai.m = M; ai.n = N;
	aai.m = M; aai.n = N;
	double lu[PN*PN];
	int P[PN];
	float d;

	printf("Filling up Matrices (%dx%d)...\n", M, N);
	fill_matrix(&a, M, N);
	for (i=0; i < a.m; i++) {
		for (j=0; j < a.n; j++) {
			lu[i*a.n+j] = a.a[i][j];
		}
	}

	ai = a; // Struct copying, not supported by VST

	eye.m = M; eye.n = N;
	for (i = 0; i < a.m; i++) {
		for (j = 0; j < a.n; j++) {
			eye.a[i][j] = i == j ? 1.0 : 0.0;
		}
	}

	printf("Running lu_dcmp...\n");
	lu_dcmp(lu, N, P, &d);

	printf("Running ainv...\n");
	ainv(&ai, &ai);
	// print_matrix(&a, "A", M, N);
	// print_matrix(&ai, "A^-1", M, N);

	printf("Checking A*A^-1...\n");
	axb(&a, &ai, &aai);
	print_matrix(&aai, "A*A^-1", M, N);

	matrix_equal(&aai, &eye, M, N);
}
