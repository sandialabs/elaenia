#ifndef MATRIXALGEBRA_
#define MATRIXALGEBRA_

#include <stdlib.h>

#ifdef __cplusplus
extern "C"{
#endif

#define MAX_N   21

typedef union {
  double ijk[3];
  struct { double i, j, k; } v;
} Vector_3;

typedef union {
  double ijks[4];
  struct { double i, j, k, s; } v;
} Vector_4;

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
  double* ap;
} Matrix_MxN;

void I(Matrix_MxN*);

void zero_mxn(Matrix_MxN*);
void zero_n(Vector_N*);

void axb(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* c);
void axb_ikj(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* C);
void aTxb(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* c);
void axbT(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* c);
void aTxbT(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* c);

void axv(const Matrix_MxN* a, const Vector_N* v, Vector_N* c);
void aTxv(const Matrix_MxN* a, const Vector_N* v, Vector_N* c);

void axk(const Matrix_MxN* a, const double k, Matrix_MxN* c);
void vxk(const Vector_N* v, const double k, Vector_N* c);

void a_add_b(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* c);
void a_add_bT(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* c);
void a_subtract_b(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* c);


void axb_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* c);
void axb_33_23(const Matrix_3x3* A, const Matrix_3x3* B, Matrix_3x3* C);
void aTxb_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* C);
void axbT_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* c);
void aTxbT_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* c);

void axv_3(const Matrix_3x3* a, const Vector_3* v, Vector_3* C);
void aTxv_3(const Matrix_3x3* a, const Vector_3* v, Vector_3* C);

void axk_33(const Matrix_3x3* a, const double k, Matrix_3x3* c);
void vxk_3(const Vector_3* v, const double k, Vector_3* c);

void v_add_v_3(const Vector_3* va, const Vector_3* vb, Vector_3* c);
void v_subtract_v_3(const Vector_3* va, const Vector_3* vb, Vector_3* c);
void v_add_k_3(const Vector_3* v, const double k, Vector_3* c);

void vxk_4(const Vector_4* a, const double k, Vector_4* c);

void v_dotx_v_3(const Vector_3* a, const Vector_3* b, Vector_3* c);


void zero_3(Vector_3* v);


void diag_matrix(const Vector_N* v, Matrix_MxN* a);
void diag_vector(const Matrix_MxN* a, Vector_N* v);


void unit_3(const Vector_3* v, Vector_3* u);
double norm_3(const Vector_3* v);

void unit_4(const Vector_4* a, Vector_4* u);
double norm_4(const Vector_4* a);

void cross(const Vector_3* a, const Vector_3* b, Vector_3* c);

double dot(const Vector_3* a, const Vector_3* b);

double sum_3(Vector_3* a);
double sum_4(Vector_4* a);


void ainv(Matrix_MxN* a, const Matrix_MxN* ai __attribute__((unused)));
void ainv_33(const Matrix_3x3* a, Matrix_3x3* c);


void diag_33(const Vector_3* v, Matrix_3x3* a);
void diag_31(const Matrix_3x3* a, Vector_3* v);

void set_33(Matrix_MxN* a, const Matrix_3x3* a33, const int r, const int c);
void get_33(const Matrix_MxN* a, Matrix_3x3* a33, const int r, const int c);

void set_3(Vector_N* v, const Vector_3* v3, const int i);
void get_3(const Vector_N* v, Vector_3* v3, const int i);


#ifdef __cplusplus
}
#endif

#endif
