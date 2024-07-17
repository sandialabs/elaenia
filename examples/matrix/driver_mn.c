#include <stdio.h>
#include <stdlib.h>
#include "Matrix_Algebra.h"

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
		printf("Bad dimensions\n");
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

int main(int argc, char *argv[]) {
	int equal;
	int M = 10;
	int N = 10;
	Matrix_MxN a, b, c1, c2;

	printf("Running for %dx%d...\n", M, N);
	fill_matrix(&a, M, N);
	fill_matrix(&b, M, N);
	printf("Running axb...\n");
	// axb is the same
	axb(&a, &b, &c1);
	printf("Running axb_ikj...\n");
	// As these four commands
	c2.m = M;
	c2.n = N;
    zero_mxn(&c2);
	axb_ikj(&a, &b, &c2);

	// Check for equality
	equal = matrix_equal(&c1, &c2, M, N);
	if (!equal) {
		printf("Not equal\n");
		print_matrix(&c1, "c1", M, N);
		print_matrix(&c2, "c2", M, N);
	}
	return 0;
}
