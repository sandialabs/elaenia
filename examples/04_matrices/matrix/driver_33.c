#include <stdio.h>
#include <stdlib.h>
#include "Matrix_Algebra.h"

/* Fills a matrix with uniform(-1,1) */
int fill_matrix_33(Matrix_3x3 *a)
{
	int i, j;
	for (i = 0; i < 3; i++) {
		for (j = 0; j < 3; j++) {
			a->a[i][j] = (double) rand() / RAND_MAX * 2.0 - 1.0;
		}
	}
	return 0;
}

/* Checks for bitwise equality */
int matrix_equal_33(Matrix_3x3 *a, Matrix_3x3 *b)
{
	int i, j;
	for (i = 0; i < 3; i++) {
		for (j = 0; j < 3; j++) {
			if (a->a[i][j] != b->a[i][j]) {
				printf("at (%d,%d) %a != %a\n",
				       i, j, a->a[i][j], b->a[i][j]);
				return 0;
			}
		}
	}
	return 1;
}

void print_matrix_33(Matrix_3x3 *a, const char* msg)
{
	int i, j;
	printf("%s = [\n", msg);
	for (i = 0; i < 3; i++) {
		printf("  ");
		for (j = 0; j < 3; j++) {
			if (i == 2 && j == 2) {
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
	printf("Running 3x3...\n");
	Matrix_3x3 a, b, c1, c2;
	fill_matrix_33(&a);
	fill_matrix_33(&b);
	axb_33(&a, &b, &c1);
	axb_33_23(&a, &b, &c2);
	equal = matrix_equal_33(&c1, &c2);
	if (!equal) {
		printf("Not equal\n");
		print_matrix_33(&c1, "c1");
		print_matrix_33(&c2, "c2");
	}	
	printf("Complete\n");
	return 0;
}
