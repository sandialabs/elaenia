#ifndef MATRIXALGEBRA_
#define MATRIXALGEBRA_

#include <string.h>

#ifdef __cplusplus
extern "C"{
#endif

#define MAX_N   20

typedef union {
  double ijk[3];
  struct { double i, j, k; } v;
} Vector_3;

typedef union {
  double a[3][3];
  struct { double _11, _12, _13, _21, _22, _23, _31, _32, _33; } s;
} Matrix_3x3;

// Unused here
typedef struct {
  int m, n;
  double a[MAX_N][MAX_N];
  double* ap;
} Matrix_MxN;

void a_add_b_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* C);
void  axb_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* C);
void aTxb_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* C);
void axbT_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* C);
void ainv_33(const Matrix_3x3* a, Matrix_3x3* c);
void diag_33(const Vector_3* v, Matrix_3x3* a);

#ifdef __cplusplus
}
#endif

#endif
