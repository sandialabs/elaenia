#ifndef MATRIXALGEBRA_
#define MATRIXALGEBRA_

#include <stdlib.h>

#ifdef __cplusplus
extern "C"{
#endif

#define MAX_N   20

typedef union {
  double ijk[3];
  struct { double i, j, k; } v; // Notational convenience
} Vector_3;

typedef struct {
  int m, n;
  double a[MAX_N];
} Vector_N;

typedef union {
  double a[3][3];
  struct { double _11, _12, _13, _21, _22, _23, _31, _32, _33; } s;
} Matrix_3x3;

typedef struct {
  int m, n;
  double a[MAX_N][MAX_N];
  double* ap; // vestigal from old (pre-1990) C, embedded systems, historical
} Matrix_MxN;

void axb(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* c);

void lu_dcmp(double *a, const int n, int *indx, float *d);
void lu_bksb(const double *a, const int n, const int *indx, double *b);
void ainv(Matrix_MxN* a, const Matrix_MxN* ai __attribute__((unused)));

#ifdef __cplusplus
}
#endif

#endif
