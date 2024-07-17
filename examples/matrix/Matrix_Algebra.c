
#include <memory.h>
#include <math.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "Matrix_Algebra.h"

#define MAX(a,b) (a>b?a:b)

/*@
  assigns \nothing;
*/
static void Matrix_Error(const char* msg) {
  //printf doesn't work on ColdFire  printf(msg);
  //while(1);

  //printf does work on Stratix-10 Linux
  printf("%s", msg);
}

/*@
  logic integer Max(integer a, integer b) =
    a > b ? a : b;

  predicate valid_Matrix_MxN(Matrix_MxN a) =
    0 < a.m <= MAX_N &&
    0 < a.n <= MAX_N;

  predicate is_square(Matrix_MxN a) =
    a.m == a.n;

  predicate valid_Vector_N(Vector_N v) =
    0 < v.m <= MAX_N &&
    0 < v.n <= MAX_N &&
    (v.m == 1 || v.n == 1);

  predicate all_zero(Matrix_MxN *A) =
    \forall integer i, j;
      0 <= i < MAX_N && 0 <= j < MAX_N ==>
        A->a[i][j] == 0.;

  logic integer length_Vector_N(Vector_N v) =
    Max(v.m, v.n);

  lemma length_valid_Vector_N :
    \forall Vector_N v; valid_Vector_N(v) ==>
      ((v.m == 1 && v.m == length_Vector_N(v)) ||
      (v.m == length_Vector_N(v) && v.n == 1));

  // Work around unsound bug in analysis of unions
  predicate fixup_Vector_3(Vector_3 v3) =
    v3.v.i == v3.ijk[0] &&
    v3.v.j == v3.ijk[1] &&
    v3.v.k == v3.ijk[2];

*/

/*@
  requires \valid(&s[0..n - 1]);
  assigns s[0..n - 1] \from c;
  assigns \result \from s;
  ensures \forall integer i; 0 <= i < n ==> s[i] == c;
  ensures \result == s;
*/
double *memset_double(double *s, const double c, const size_t n) {
  #ifdef __FRAMAC__
  size_t i;
  /*@
    loop invariant 0 <= i <= n;
    loop invariant \forall integer k; 0 <= k < i ==> s[k] == c;
    loop assigns i, s[0..n - 1];
    loop variant n-i;
  */
  for(i=0; i < n; i++) {
    s[i] = c;
  }
  return s;
  #else
  return (double *)memset((double *)s, c, n*sizeof(double));
  #endif
}


/*@
  requires \valid(a);
  requires valid_Matrix_MxN(*a);
  requires is_square(*a);
  assigns a->a[0..(a->m)-1][0..(a->n)-1];
  ensures diagonal:
    \forall integer i; 0 <= i < a->m ==>
      a->a[i][i] == (double)1.0;
  ensures off_diagonal:
    \forall integer i, j; 0 <= i < a->m && 0 <= j < a->n ==>
      i != j ==>
      a->a[i][j] == (double)0.0;
*/
void I(Matrix_MxN* a) {

  int i;

  if (a->m != a->n) {
    //@ assert \false;
    Matrix_Error("eye - size error\n");
  }

  /*@
    loop invariant 0 <= i <= a->m;
    loop invariant
      \forall integer ix, jx; 0 <= ix < i && 0 <= jx < a->n ==>
        a->a[ix][jx] == (ix == jx ? (double)1.0 : (double)0.0);
    loop assigns i, a->a[0..(a->m)-1][0..(a->n)-1];
    loop variant (a->m)-i;
  */
  for (i=0; i<a->m; i++) {
    memset_double(a->a[i], 0, a->n);
    a->a[i][i] = 1.0;
  }
}

/*@
  requires \valid_read(v);
  requires valid_Vector_N(*v);
  requires \valid(a);
  requires \separated(v, a);
  assigns a->m, a->n;
  assigns a->a[0..length_Vector_N(*v)-1][0..length_Vector_N(*v)-1];
  ensures valid_Matrix_MxN(*a);
  ensures a->m == Max(v->m, v->n);
  ensures a->n == Max(v->m, v->n);
  ensures is_square(*a);
  ensures diagonal:
    \forall integer i; 0 <= i < a->m ==>
      a->a[i][i] == v->a[i];
  ensures off_diagonal:
    \forall integer i, j; 0 <= i < a->m && 0 <= j < a->n ==>
      i != j ==>
      a->a[i][j] == (double)0.0;
*/
void diag_matrix(const Vector_N* v, Matrix_MxN* a) {

  int i;

  a->m = a->n = (v->n == 1 ? v->m : v->n);

  /*@
    loop invariant 0 <= i <= a->m;
    loop invariant
      \forall integer ix, jx; 0 <= ix < i && 0 <= jx < a->n ==>
        a->a[ix][jx] == (ix == jx ? v->a[ix] : (double)0.0);
    loop assigns i, a->a[0..(a->m)-1][0..(a->n)-1];
    loop variant (a->m)-i;
  */
  for (i=0; i<a->m; i++) {
    memset_double(a->a[i], 0.0, a->n);
    a->a[i][i] = v->a[i];
  }
}

/*@
  requires \valid_read(a);
  requires valid_Matrix_MxN(*a);
  requires is_square(*a);
  requires \valid(v);
  requires \separated(v, a);
  assigns v->m, v->n;
  assigns v->a[0.. a->m-1];
  ensures v->m == a->m;
  ensures v->n == 1;
  ensures length_Vector_N(*v) == a->m;
  ensures diagonal:
    \forall integer i; 0 <= i < a->m ==>
      v->a[i] == a->a[i][i];
*/
void diag_vector(const Matrix_MxN* a, Vector_N* v) {

  int i;

  if (a->m != a->n) {
    //@ assert \false;
    Matrix_Error("diag_vector - size error\n");
  }

  v->m = a->m;
  v->n = 1;

  /*@
    loop invariant 0 <= i <= a->m;
    loop invariant
      \forall integer ix; 0 <= ix < i ==>
        v->a[ix] == a->a[ix][ix];
    loop assigns i, v->a[0..(a->m)-1];
    loop variant (a->m)-i;
  */
  for (i=0; i<a->m; i++) {
    v->a[i] = a->a[i][i];
  }

}


/*@
  requires \valid_read(a33);
  requires \valid(a);
  requires valid_Matrix_MxN(*a);
  requires \separated(a33, a);
  requires 0 <= r;
  requires r+3 <= a->m;
  requires 0 <= c;
  requires c+3 <= a->n;
  assigns a->a[r..r+2][c..c+2];
  ensures
    \forall integer i, j;
      0 <= i < 3 && 0 <= j < 3 ==>
      a->a[r+i][c+j] == a33->a[i][j];
*/
void set_33(Matrix_MxN* a, const Matrix_3x3* a33, const int r, const int c) {

  if ( (r+3 > a->m) || (c+3 > a->n) || (r < 0) || (c < 0) ) {
    //@ assert \false;
    Matrix_Error("set_33 - size error\n");
  }

  a->a[r+0][c+0] = a33->a[0][0];
  a->a[r+0][c+1] = a33->a[0][1];
  a->a[r+0][c+2] = a33->a[0][2];
  a->a[r+1][c+0] = a33->a[1][0];
  a->a[r+1][c+1] = a33->a[1][1];
  a->a[r+1][c+2] = a33->a[1][2];
  a->a[r+2][c+0] = a33->a[2][0];
  a->a[r+2][c+1] = a33->a[2][1];
  a->a[r+2][c+2] = a33->a[2][2];

}

/*@
  requires \valid(a33);
  requires \valid_read(a);
  requires valid_Matrix_MxN(*a);
  requires \separated(a33, a);
  requires 0 <= r;
  requires r+3 <= a->m;
  requires 0 <= c;
  requires c+3 <= a->n;
  assigns a33->a[0..2][0..2];
  ensures
    \forall integer i, j;
      0 <= i < 3 && 0 <= j < 3 ==>
      a33->a[i][j] == a->a[r+i][c+j];
*/
void get_33(const Matrix_MxN* a, Matrix_3x3* a33, const int r, const int c) {
  if ((r + 3 > a->m) || (c + 3 > a->n) || r < 0 || c < 0) {
    //@ assert \false;
    Matrix_Error("get_33 - size error\n");
  }

  a33->a[0][0] = a->a[r+0][c+0];
  a33->a[0][1] = a->a[r+0][c+1];
  a33->a[0][2] = a->a[r+0][c+2];
  a33->a[1][0] = a->a[r+1][c+0];
  a33->a[1][1] = a->a[r+1][c+1];
  a33->a[1][2] = a->a[r+1][c+2];
  a33->a[2][0] = a->a[r+2][c+0];
  a33->a[2][1] = a->a[r+2][c+1];
  a33->a[2][2] = a->a[r+2][c+2];

}

/*@
  requires \valid_read(v3);
  requires \valid(v);
  requires valid_Vector_N(*v);
  requires \separated(v3, v);
  requires 0 <= i;
  requires i+3 <= length_Vector_N(*v);
  assigns v->a[i..i+2];
  ensures
    \forall integer k;
      0 <= k < 3 ==>
      v->a[i+k] == v3->ijk[k];
*/
void set_3(Vector_N* v, const Vector_3* v3, const int i) {

  //@ assert no_wp: fixup_Vector_3(*v3);
  v->a[i+0] = v3->v.i;
  v->a[i+1] = v3->v.j;
  v->a[i+2] = v3->v.k;

}

/*@
  requires \valid(v3);
  requires \valid_read(v);
  requires valid_Vector_N(*v);
  requires \separated(v3, v);
  requires 0 <= i;
  requires i+3 <= length_Vector_N(*v);
  assigns v3->ijk[i..i+2];
  assigns v3->v.i, v3->v.j, v3->v.k;
  ensures
    \forall integer k;
      0 <= k < 3 ==>
      v3->ijk[k] == v->a[i+k];
*/
void get_3(const Vector_N* v, Vector_3* v3, const int i) {

  v3->v.i = v->a[i+0];
  v3->v.j = v->a[i+1];
  v3->v.k = v->a[i+2];
  //@ assert no_wp: fixup_Vector_3(*v3);

}

/*@
  requires \valid(a);
  requires \valid_read(v);
  requires \separated(a, v);
  assigns *a;
*/
void diag_33(const Vector_3* v, Matrix_3x3* a) {

  #ifdef __FRAMAC__
  memset_double(a->a[0], 0, 3);
  memset_double(a->a[1], 0, 3);
  memset_double(a->a[2], 0, 3);
  #else
  memset(a, 0, 9*sizeof(double));
  #endif
  a->s._11 = v->v.i;
  a->s._22 = v->v.j;
  a->s._33 = v->v.k;

}

/*@
  requires \valid_read(a);
  requires \valid(v);
  requires \separated(a, v);
  assigns *v;
*/
void diag_31(const Matrix_3x3* a, Vector_3* v) {

  v->v.i = a->s._11;
  v->v.j = a->s._22;
  v->v.k = a->s._33;

}

/*@
  requires \valid(a);
  requires valid_Matrix_MxN(*a);
  assigns a->a[0..a->m-1][0..a->n-1];
  ensures zeroes:
    \forall integer i, j; 0 <= i < a->m && 0 <= j < a->n ==>
      a->a[i][j] == (double)0.0;
*/
void zero_mxn(Matrix_MxN* a) {

  int i;

  /*@
    loop invariant 0 <= i <= a->m;
    loop invariant
      \forall integer ix, jx; 0 <= ix < i && 0 <= jx < a->n ==>
        a->a[ix][jx] == (double)0.0;
    loop assigns i, a->a[0..(a->m)-1][0..(a->n)-1];
    loop variant (a->m)-i;
  */
  for (i=0; i<a->m; i++) {
    memset_double(a->a[i], 0, a->n);
  }

}

/*@
  requires \valid(v);
  requires valid_Vector_N(*v);
  assigns v->a[0..length_Vector_N(*v)-1];
  ensures zeroes:
    \forall integer i; 0 <= i < length_Vector_N(*v) ==>
      v->a[i] == (double)0.0;
*/
void zero_n(Vector_N* v) {

  memset_double(v->a, 0, MAX(v->m, v->n));

}

/* A useful predicate to describe "finiteness" of floating-point
 * values with respect to real numbers */

/*@ predicate dbl_expr_finite(real x) =
  @   \abs(x) <= 0x1.fffffffffffffp+1023; // Max double precision float, ~1.8e308
  @ predicate flt_expr_finite(real x) =
  @   \abs(x) <= 0x1.fffffep+127; // Max single precision float, ~3.4e38
*/


/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \is_finite(a->v.i);
  requires \is_finite(a->v.j);
  requires \is_finite(a->v.k);
  assigns \nothing;
*/
double dot(const Vector_3* a, const Vector_3* b) {
  return a->v.i*b->v.i + a->v.i*b->v.j + a->v.k*b->v.k;
}

/*@ requires \valid_read(a);
  @ requires \is_finite(a->v.i);
  @ requires \is_finite(a->v.j);
  @ requires \is_finite(a->v.k);
  @ requires
  @   \let i2   = (double)(a->v.i * a->v.i);
  @   \let j2   = (double)(a->v.j * a->v.j);
  @   \let k2   = (double)(a->v.k * a->v.k);
  @   \let ij2  = (double)(i2 + j2);
  @   \let ijk2 = (double)(ij2 + k2);
  @   \is_finite(i2) && \is_finite(j2) && \is_finite(k2) &&
  @     \is_finite(ij2) && \is_finite(ijk2);
  @ requires dbl_expr_finite(a->v.i*a->v.i + a->v.j*a->v.j + a->v.k*a->v.k);
  @ assigns errno;
  @ ensures \is_finite(\result);
  @ ensures \result >= 0.0;
  @ ensures errno == \old(errno);
*/
double norm_3(const Vector_3* a) {
  return sqrt(a->v.i*a->v.i + a->v.j*a->v.j + a->v.k*a->v.k);
}

/*@ requires \valid_read(a);
  @ requires -1e150 <= a->v.i && a->v.i <= 1e150;
  @ requires -1e150 <= a->v.j && a->v.j <= 1e150;
  @ requires -1e150 <= a->v.k && a->v.k <= 1e150;
  @ requires -1e150 <= a->v.s && a->v.s <= 1e150;
  @ ensures (a->v.i*a->v.i + a->v.j*a->v.j + a->v.k*a->v.k + a->v.s*a->v.s) <= 4e300;
  @ ensures 0.0 <= (a->v.i*a->v.i + a->v.j*a->v.j + a->v.k*a->v.k + a->v.s*a->v.s);
  @ assigns errno;
*/
double norm_4(const Vector_4* a) {
  return sqrt(a->v.i*a->v.i + a->v.j*a->v.j + a->v.k*a->v.k + a->v.s*a->v.s);
}

/*@
  requires \valid_read(a);
  requires \valid(u);
  assigns *u;
*/
void unit_3(const Vector_3* a, Vector_3* u) {
  vxk_3(a, 1/norm_3(a), u);
}

/*@
  requires \valid_read(a);
  requires \valid(u);
  assigns *u;
*/
void unit_4(const Vector_4* a, Vector_4* u) {
  vxk_4(a, 1/norm_4(a), u);
}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void axb(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* C) {

  int r, c, i;
  Matrix_MxN ret = {a->m, b->n};

  if (a->n != b->m) {
    Matrix_Error("matrix_multiply - size error axb\n");
  }

  for (r=0; r<a->m; r++) {
    for (c=0; c<b->n; c++) {
      ret.a[r][c] = 0.0;
      for (i=0; i<a->n; i++) ret.a[r][c] += a->a[r][i]*b->a[i][c];
    }
  }
  *C = ret;
}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires all_zero(C);
  assigns *C;
*/
void axb_ikj(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* C) {

  int i, j, k;
  if (a->n != b->m) {
    Matrix_Error("matrix_multiply - size error axb\n");
  }

  C->m = a->m;
  C->n = b->n;
  for (i=0; i<a->m; i++) {
    for (k=0; k<b->n; k++) {
      for (j=0; j<a->n; j++) {
        C->a[i][j] += a->a[i][k]*b->a[k][j];
      }
    }
  }
}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires all_zero(C);
  assigns *C;
*/
void axb_kij(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* C) {

  int i, j, k;
  if (a->n != b->m) {
    Matrix_Error("matrix_multiply - size error axb\n");
  }

  C->m = a->m;
  C->n = b->n;
  for (k=0; i<a->m; i++) {
    for (i=0; k<b->n; k++) {
      for (j=0; j<a->n; j++) {
        C->a[i][j] += a->a[i][k]*b->a[k][j];
      }
    }
  }
}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void aTxb(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* C) {

  int r, c, i;
  Matrix_MxN ret = {a->n, b->n};

  if (a->m != b->m) {
    Matrix_Error("matrix multiply - size error aTxb\n");
  }

  for (r=0; r<a->n; r++) {
    for (c=0; c<b->n; c++) {
      ret.a[r][c] = 0.0;
      for (i=0; i<a->m; i++) ret.a[r][c] += a->a[i][r]*b->a[i][c];
    }
  }

  *C = ret;

}

// BLAS computes
// C = C + A * B
/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void axbT(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* C) {

  int r, c, i;
  Matrix_MxN ret = {a->m, b->m};

  if (a->n != b->n) {
    Matrix_Error("matrix multiply - size error axbT\n");
  }

  for (r=0; r<a->m; r++) {
    for (c=0; c<b->m; c++) {
      ret.a[r][c] = 0.0;
      for (i=0; i<a->n; i++) ret.a[r][c] += a->a[r][i]*b->a[c][i];
    }
  }

  *C = ret;

}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void aTxbT(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* C) {

  int r, c, i;
  Matrix_MxN ret = {a->n, b->m};

  if (a->m != b->n) {
    Matrix_Error("matrix multiply - size error aTxbT\n");
  }

  for (r=0; r<a->n; r++) {
    for (c=0; c<b->m; c++) {
      ret.a[r][c] = 0.0;
      for (i=0; i<a->m; i++) ret.a[r][c] += a->a[i][r]*b->a[c][i];
    }
  }

  *C = ret;

}

/*@
  requires \valid_read(a);
  requires \valid_read(v);
  requires \valid(C);
  assigns *C;
*/
void axv(const Matrix_MxN* a, const Vector_N* v, Vector_N* C) {

  int r, i;
  Vector_N ret = {a->m, v->n};

  if (a->n != v->m) {
    Matrix_Error("matrix_multiply - size error axv\n");
  }

  for (r=0; r<a->m; r++) {
    ret.a[r] = 0.0;
    for (i=0; i<v->m; i++) ret.a[r] += a->a[r][i]*v->a[i];
  }

  *C = ret;

}

/*@
  requires \valid_read(a);
  requires \valid_read(v);
  requires \valid(C);
  assigns *C;
*/
void aTxv(const Matrix_MxN* a, const Vector_N* v, Vector_N* C) {

  int r, i;
  Vector_N ret = {a->n, v->n};

  if (a->m != v->m) {
    Matrix_Error("matrix multiply - size error aTxv\n");
  }

  for (r=0; r<a->n; r++) {
    ret.a[r] = 0.0;
    for (i=0; i<v->m; i++) ret.a[r] += a->a[i][r]*v->a[i];
  }

  *C = ret;

}

/*@
  requires \valid_read(a);
  requires \valid(C);
  assigns *C;
*/
void axk(const Matrix_MxN* a, const double k, Matrix_MxN* C) {

  int r, c;
  Matrix_MxN ret = {a->m, a->n};

  for (r=0; r<a->m; r++) {
    for (c=0; c<a->n; c++) {
      ret.a[r][c] = a->a[r][c] * k;
    }
  }

  *C = ret;
}

/*@
  requires \valid_read(v);
  requires \valid(C);
  assigns *C;
*/
void vxk(const Vector_N* v, const double k, Vector_N* C) {

  int i;
  Vector_N ret = {v->m, v->n};

  for (i=0; i<v->m; i++) {
    ret.a[i] = v->a[i] * k;
  }

  *C = ret;
}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void a_add_b(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* C) {

  int r, c;
  Matrix_MxN ret = {a->m, a->n};

  if ((a->m != b->m) || (a->n != b->n)) {
    Matrix_Error("matrix multiply - size error a_add_b\n");
  }

  for (r=0; r<a->m; r++) {
    for (c=0; c<a->n; c++) {
      ret.a[r][c] = a->a[r][c] + b->a[r][c];
    }
  }

  *C = ret;
}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void a_subtract_b(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* C) {

  int r, c;
  Matrix_MxN ret = {a->m, a->n};

  if ((a->m != b->m) || (a->n != b->n)) {
    Matrix_Error("matrix multiply - size error a_subtract_b\n");
  }

  for (r=0; r<a->m; r++) {
    for (c=0; c<a->n; c++) {
      ret.a[r][c] = a->a[r][c] - b->a[r][c];
    }
  }

  *C = ret;
}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void a_add_bT(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* C) {

  int r, c;
  Matrix_MxN ret = {a->m, a->n};

  if ((a->m != b->n) || (a->n != b->m)) {
    Matrix_Error("matrix multiply - size error a_add_bT\n");
  }

for (r=0; r<a->m; r++) {
    for (c=0; c<a->n; c++) {
      ret.a[r][c] = a->a[r][c] + b->a[c][r];
    }
  }

  *C = ret;
}

/*@
  requires \valid(v);
  assigns *v;
*/
void zero_3(Vector_3* v) {

  v->v.i = 0;
  v->v.j = 0;
  v->v.k = 0;

}

/*@
  requires \valid_read(va);
  requires \valid_read(vb);
  requires \valid(C);
  assigns *C;
*/
void v_add_v_3(const Vector_3* va, const Vector_3* vb, Vector_3* C) {

  Vector_3 ret;

  ret.v.i = va->v.i + vb->v.i;
  ret.v.j = va->v.j + vb->v.j;
  ret.v.k = va->v.k + vb->v.k;

  *C = ret;

}

/*@
  requires \valid_read(v);
  requires \valid(C);
  assigns *C;
*/
void v_add_k_3(const Vector_3* v, const double k, Vector_3* C) {

  Vector_3 ret;

  ret.v.i = v->v.i + k;
  ret.v.j = v->v.j + k;
  ret.v.k = v->v.k + k;

  *C = ret;

}

/*@
  requires \valid_read(va);
  requires \valid_read(vb);
  requires \valid(C);
  assigns *C;
*/
void v_subtract_v_3(const Vector_3* va, const Vector_3* vb, Vector_3* C) {

  Vector_3 ret;

  ret.v.i = va->v.i - vb->v.i;
  ret.v.j = va->v.j - vb->v.j;
  ret.v.k = va->v.k - vb->v.k;

  *C = ret;

}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void axb_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* C) {

  Matrix_3x3 ret;

  ret.s._11 = a->s._11*b->s._11 + a->s._12*b->s._21 + a->s._13*b->s._31;
  ret.s._12 = a->s._11*b->s._12 + a->s._12*b->s._22 + a->s._13*b->s._32;
  ret.s._13 = a->s._11*b->s._13 + a->s._12*b->s._23 + a->s._13*b->s._33;

  ret.s._21 = a->s._21*b->s._11 + a->s._22*b->s._21 + a->s._23*b->s._31;
  ret.s._22 = a->s._21*b->s._12 + a->s._22*b->s._22 + a->s._23*b->s._32;
  ret.s._23 = a->s._21*b->s._13 + a->s._22*b->s._23 + a->s._23*b->s._33;

  ret.s._31 = a->s._31*b->s._11 + a->s._32*b->s._21 + a->s._33*b->s._31;
  ret.s._32 = a->s._31*b->s._12 + a->s._32*b->s._22 + a->s._33*b->s._32;
  ret.s._33 = a->s._31*b->s._13 + a->s._32*b->s._23 + a->s._33*b->s._33;

  *C = ret;

}

/* Using Laderman multiplication to compute 23 flops instead of 27
 * Taken from
 * https://stackoverflow.com/questions/10827209/ladermans-3x3-matrix-multiplication-with-only-23-multiplications-is-it-worth-i 
 */
void axb_33_23(const Matrix_3x3* A, const Matrix_3x3* B, Matrix_3x3* C) {
	
	double m[24]; // not off by one, just wanted to match the index from the paper
	
	m[1 ]= (A->a[0][0]+A->a[0][1]+A->a[0][2]-A->a[1][0]-A->a[1][1]-A->a[2][1]-A->a[2][2])*B->a[1][1];
	m[2 ]= (A->a[0][0]-A->a[1][0])*(-B->a[0][1]+B->a[1][1]);
	m[3 ]= A->a[1][1]*(-B->a[0][0]+B->a[0][1]+B->a[1][0]-B->a[1][1]-B->a[1][2]-B->a[2][0]+B->a[2][2]);
	m[4 ]= (-A->a[0][0]+A->a[1][0]+A->a[1][1])*(B->a[0][0]-B->a[0][1]+B->a[1][1]);
	m[5 ]= (A->a[1][0]+A->a[1][1])*(-B->a[0][0]+B->a[0][1]);
	m[6 ]= A->a[0][0]*B->a[0][0];
	m[7 ]= (-A->a[0][0]+A->a[2][0]+A->a[2][1])*(B->a[0][0]-B->a[0][2]+B->a[1][2]);
	m[8 ]= (-A->a[0][0]+A->a[2][0])*(B->a[0][2]-B->a[1][2]);
	m[9 ]= (A->a[2][0]+A->a[2][1])*(-B->a[0][0]+B->a[0][2]);
	m[10]= (A->a[0][0]+A->a[0][1]+A->a[0][2]-A->a[1][1]-A->a[1][2]-A->a[2][0]-A->a[2][1])*B->a[1][2];
	m[11]= A->a[2][1]*(-B->a[0][0]+B->a[0][2]+B->a[1][0]-B->a[1][1]-B->a[1][2]-B->a[2][0]+B->a[2][1]);
	m[12]= (-A->a[0][2]+A->a[2][1]+A->a[2][2])*(B->a[1][1]+B->a[2][0]-B->a[2][1]);
	m[13]= (A->a[0][2]-A->a[2][2])*(B->a[1][1]-B->a[2][1]);
	m[14]= A->a[0][2]*B->a[2][0];
	m[15]= (A->a[2][1]+A->a[2][2])*(-B->a[2][0]+B->a[2][1]);
	m[16]= (-A->a[0][2]+A->a[1][1]+A->a[1][2])*(B->a[1][2]+B->a[2][0]-B->a[2][2]);
	m[17]= (A->a[0][2]-A->a[1][2])*(B->a[1][2]-B->a[2][2]);
	m[18]= (A->a[1][1]+A->a[1][2])*(-B->a[2][0]+B->a[2][2]);
	m[19]= A->a[0][1]*B->a[1][0];
	m[20]= A->a[1][2]*B->a[2][1];
	m[21]= A->a[1][0]*B->a[0][2];
	m[22]= A->a[2][0]*B->a[0][1];
	m[23]= A->a[2][2]*B->a[2][2];

	C->a[0][0] = m[6]+m[14]+m[19];
  	C->a[0][1] = m[1]+m[4]+m[5]+m[6]+m[12]+m[14]+m[15];
  	C->a[0][2] = m[6]+m[7]+m[9]+m[10]+m[14]+m[16]+m[18];
  	C->a[1][0] = m[2]+m[3]+m[4]+m[6]+m[14]+m[16]+m[17];
  	C->a[1][1] = m[2]+m[4]+m[5]+m[6]+m[20];
  	C->a[1][2] = m[14]+m[16]+m[17]+m[18]+m[21];
  	C->a[2][0] = m[6]+m[7]+m[8]+m[11]+m[12]+m[13]+m[14];
  	C->a[2][1] = m[12]+m[13]+m[14]+m[15]+m[22];
  	C->a[2][2] = m[6]+m[7]+m[8]+m[9]+m[23];    
}


/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void aTxb_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* C) {

  Matrix_3x3 ret;

  ret.s._11 = a->s._11*b->s._11 + a->s._21*b->s._21 + a->s._31*b->s._31;
  ret.s._12 = a->s._11*b->s._12 + a->s._21*b->s._22 + a->s._31*b->s._32;
  ret.s._13 = a->s._11*b->s._13 + a->s._21*b->s._23 + a->s._31*b->s._33;

  ret.s._21 = a->s._12*b->s._11 + a->s._22*b->s._21 + a->s._32*b->s._31;
  ret.s._22 = a->s._12*b->s._12 + a->s._22*b->s._22 + a->s._32*b->s._32;
  ret.s._23 = a->s._12*b->s._13 + a->s._22*b->s._23 + a->s._32*b->s._33;

  ret.s._31 = a->s._13*b->s._11 + a->s._23*b->s._21 + a->s._33*b->s._31;
  ret.s._32 = a->s._13*b->s._12 + a->s._23*b->s._22 + a->s._33*b->s._32;
  ret.s._33 = a->s._13*b->s._13 + a->s._23*b->s._23 + a->s._33*b->s._33;

  *C = ret;

}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void axbT_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* C) {

  Matrix_3x3 ret;

  ret.s._11 = a->s._11*b->s._11 + a->s._12*b->s._12 + a->s._13*b->s._13;
  ret.s._12 = a->s._11*b->s._21 + a->s._12*b->s._22 + a->s._13*b->s._23;
  ret.s._13 = a->s._11*b->s._31 + a->s._12*b->s._32 + a->s._13*b->s._33;

  ret.s._21 = a->s._21*b->s._11 + a->s._22*b->s._12 + a->s._23*b->s._13;
  ret.s._22 = a->s._21*b->s._21 + a->s._22*b->s._22 + a->s._23*b->s._23;
  ret.s._23 = a->s._21*b->s._31 + a->s._22*b->s._32 + a->s._23*b->s._33;

  ret.s._31 = a->s._31*b->s._11 + a->s._32*b->s._12 + a->s._33*b->s._13;
  ret.s._32 = a->s._31*b->s._21 + a->s._32*b->s._22 + a->s._33*b->s._23;
  ret.s._33 = a->s._31*b->s._31 + a->s._32*b->s._32 + a->s._33*b->s._33;

  *C = ret;

}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void aTxbT_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* C) {

  Matrix_3x3 ret;

  ret.s._11 = a->s._11*b->s._11 + a->s._21*b->s._12 + a->s._31*b->s._13;
  ret.s._12 = a->s._11*b->s._21 + a->s._21*b->s._22 + a->s._31*b->s._23;
  ret.s._13 = a->s._11*b->s._31 + a->s._21*b->s._32 + a->s._31*b->s._33;

  ret.s._21 = a->s._12*b->s._11 + a->s._22*b->s._12 + a->s._32*b->s._13;
  ret.s._22 = a->s._12*b->s._21 + a->s._22*b->s._22 + a->s._32*b->s._23;
  ret.s._23 = a->s._12*b->s._31 + a->s._22*b->s._32 + a->s._32*b->s._33;

  ret.s._31 = a->s._13*b->s._11 + a->s._23*b->s._12 + a->s._33*b->s._13;
  ret.s._32 = a->s._13*b->s._21 + a->s._23*b->s._22 + a->s._33*b->s._23;
  ret.s._33 = a->s._13*b->s._31 + a->s._23*b->s._32 + a->s._33*b->s._33;

  *C = ret;

}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void axv_3(const Matrix_3x3* a, const Vector_3* b, Vector_3* C) {

  Vector_3 ret;

  ret.v.i = a->s._11*b->v.i + a->s._12*b->v.j + a->s._13*b->v.k;
  ret.v.j = a->s._21*b->v.i + a->s._22*b->v.j + a->s._23*b->v.k;
  ret.v.k = a->s._31*b->v.i + a->s._32*b->v.j + a->s._33*b->v.k;

  *C = ret;

}

/*@
  requires \valid_read(a);
  requires \valid_read(b);
  requires \valid(C);
  assigns *C;
*/
void aTxv_3(const Matrix_3x3* a, const Vector_3* b, Vector_3* C) {

  Vector_3 ret;

  ret.v.i = a->s._11*b->v.i + a->s._21*b->v.j + a->s._31*b->v.k;
  ret.v.j = a->s._12*b->v.i + a->s._22*b->v.j + a->s._32*b->v.k;
  ret.v.k = a->s._13*b->v.i + a->s._23*b->v.j + a->s._33*b->v.k;

  *C = ret;

}

/*@
  requires \valid_read(a);
  requires \valid(c);
  assigns *c;
*/
void ainv_33(const Matrix_3x3* a, Matrix_3x3* c) {
  double di = 1 / (a->s._11*a->s._22*a->s._33 + a->s._12*a->s._23*a->s._31 + a->s._13*a->s._21*a->s._32
                 - a->s._13*a->s._22*a->s._31 - a->s._12*a->s._21*a->s._33 - a->s._11*a->s._23*a->s._32);

  c->s._11 =  di * (a->s._22*a->s._33 - a->s._23*a->s._32);
  c->s._12 = -di * (a->s._12*a->s._33 - a->s._13*a->s._32);
  c->s._13 =  di * (a->s._12*a->s._23 - a->s._13*a->s._22);
  c->s._21 = -di * (a->s._21*a->s._33 - a->s._23*a->s._31);
  c->s._22 =  di * (a->s._11*a->s._33 - a->s._13*a->s._31);
  c->s._23 = -di * (a->s._11*a->s._23 - a->s._13*a->s._21);
  c->s._31 =  di * (a->s._21*a->s._32 - a->s._22*a->s._31);
  c->s._32 = -di * (a->s._11*a->s._32 - a->s._12*a->s._31);
  c->s._33 =  di * (a->s._11*a->s._22 - a->s._12*a->s._21);
}

/*@ requires \valid_read(v1);
  @ requires \valid_read(v2);
  @ requires \valid(c);
  @ assigns c->v.i, c->v.j, c->v.k;
*/
void v_dotx_v_3(const Vector_3* v1, const Vector_3* v2, Vector_3* c) {

  c->v.i = v1->v.i * v2->v.i;
  c->v.j = v1->v.j * v2->v.j;
  c->v.k = v1->v.k * v2->v.k;

}


/*@ requires \valid_read(v);
  @ requires \valid(c);
  @ requires -1000.0 <= v->v.i && v->v.i <= 1000.0;
  @ requires -1000.0 <= v->v.j && v->v.j <= 1000.0;
  @ requires -1000.0 <= v->v.k && v->v.k <= 1000.0;
  @ requires -1000.0 <= k && k <= 1000.0;
  @ requires -1000.0 <= c->v.i && c->v.i <= 1000.0;
  @ requires -1000.0 <= c->v.j && c->v.j <= 1000.0;
  @ requires -1000.0 <= c->v.k && c->v.k <= 1000.0;
  @ ensures -1e6 <= k * v->v.i <= 1e6;
  @ ensures -1e6 <= k * v->v.j <= 1e6;
  @ ensures -1e6 <= k * v->v.k <= 1e6;
  @ assigns c->v.i, c->v.j, c->v.k;
 */
void vxk_3(const Vector_3* v, const double k, Vector_3*c) {

  c->v.i = v->v.i * k;
  c->v.j = v->v.j * k;
  c->v.k = v->v.k * k;

}

/*@ requires \valid_read(v);
  @ requires \valid(c);
  @ assigns c-> v.i, c->v.j, c->v.k, c->v.s;
*/
void vxk_4(const Vector_4* v, const double k, Vector_4*c) {

  c->v.i = v->v.i * k;
  c->v.j = v->v.j * k;
  c->v.k = v->v.k * k;
  c->v.s = v->v.s * k;

}

static void lu_dcmp(double *, const int, int *, float *);
static void lu_bksb(const double *, const int, const int *, double *);

/*@
  requires \valid(a);
  assigns *a;
*/
void ainv( Matrix_MxN* a,     /* original n*n matrix that is a vector */
           const Matrix_MxN* ai __attribute__((unused)))     /* inverse of the matrix a */
{
  double a_copy[MAX_N*MAX_N];
  double ai_copy[MAX_N*MAX_N];
  int i, j, indx[MAX_N];
  double col[MAX_N];
  float d;

  for (i=0; i<a->m; i++) {
    for (j=0; j<a->n; j++) {
      a_copy[i*a->n+j] = a->a[i][j];
    }
  }

  /* Form the LU Decomposition of a_copy */
  lu_dcmp(a_copy, a->n, indx, &d);

  /* Determine the inverse of a via LU backsubstitution */
  for (j = 0; j < a->n; j++) {
    for (i = 0; i < a->n; i ++) col[i] = 0.0;
      col[j] = 1.0;
      lu_bksb(a_copy, a->n, indx, col);
      for (i = 0; i < a->n; i++) ai_copy[i*a->n+j] = col[i];
  }

  for (i=0; i<a->m; i++) {
    for (j=0; j<a->n; j++) {
      a->a[i][j] = ai_copy[i*a->n+j];
    }
  }
}

/*@
  requires \valid(a);
  requires \valid(indx);
  requires \valid(d);
  assigns *a;
  assigns *indx;
  assigns *d;
*/
/***********************************************************************
* FUNCTION: lu_dcmp
* PURPOSE:  Decompose a matrix into its upper and lower components.
* NOTES: n must be less than or equal to NS_MAT_UTIL since temporary
*        variables are dimensioned to size NS_MAT_UTIL.
***********************************************************************
*                                HISTORY
* 990503 -tjk- original version derived from a working function.
***********************************************************************/

static void lu_dcmp(
                    double *a,      /* matrix that is replaced with its LU Decomp */
                    const int n,          /* dim of the square matrix a */
                    int *indx,      /* records the row pivoting */
                    float *d)       /* +1/-1 if even/odd number of row interchanges */
{
    int i, imax, j, k;
    double big, dum, sum, temp;
    double vv[MAX_N];

#ifdef FILT_DEBUG_PRINT
    /* Print warning message if n is larger than NS_MAT_UTIL and stop*/
    if ( n > NS_MAT_UTIL )
    {
        data_log(Misc_TextStr, char_buff,
            sprintf(char_buff,
            "ERROR: matrix inverse internal dimension too small: n = %d\n", n));
        while(-1);
    }
#endif

    *d = (float)1.0;                /* no row interchanges yet */

    for (i = 0; i < n; i++){        /* loop rows to get scaling info */
        big = 0.0;
        for (j = 0; j < n; j++)
        {
            if ((temp = fabs(a[i*n+j])) > big) {
                 big = temp;
            }
        }
        if (big == 0.0)
        {
                /*This should NEVER happen in real-time operation, but just in*/
                /* case, set to something tiny*/
                big = -1e99;

#ifdef FILT_DEBUG_PRINT
                data_log(Misc_TextStr, char_buff,
            sprintf(char_buff,
            "sal: Singular matrix in function ludcmp.\n"));
                while(-1);
#endif
        }
        vv[i] = 1.0/big;
    }


    for (j = 0; j < n; j++){        /* loop over columns of Crout's */
        for (i = 0; i < j; i++){
            sum = a[i*n+j];
            for (k = 0; k < i; k++) sum -= a[i*n+k]*a[k*n+j];
            a[i*n+j] = sum;
        }
        imax = j;
        big = 0.0;
        for (i=j; i < n; i++) {
            sum= a[i*n+j];
            for (k = 0; k < j; k++) sum -= a[i*n+k]*a[k*n+j];
            a[i*n+j] = sum;
            if ( (dum = vv[i]*fabs(sum)) >= big )
            {
                big = dum;
                imax = i;
            }
        }

        if (j != imax)              /* interchange rows if necessary */
        {
            for ( k = 0; k < n; k++) {
                dum = a[imax*n+k];
                a[imax*n+k] = a[j*n+k];
                a[j*n+k] = dum;
            }
            *d = - (*d);            /* change parity of d */
            vv[imax] = vv[j];
        }

        indx[j] = imax;
        if (a[j*n+j] == 0.0) a[j*n+j] = -1e99;
        if (j != (n-1))
        {
            dum = 1.0/(a[j*n+j]);
            for (i = j + 1; i < n; i++) a[i*n+j] *= dum;
        }
    }
}

/*@
  requires \valid_read(a);
  requires \valid_read(indx);
  requires \valid(b);
  assigns *b;
*/
/***********************************************************************
* FUNCTION: lu_bksb
* PURPOSE:  Backsubstitution of an LU-decomposed matrix.
* NOTES:
***********************************************************************
*                                HISTORY
* 990503 -tjk- original version derived from a working function.
***********************************************************************/

static void lu_bksb(
                    const double *a,      /* LU Decomposition of original a matrix */
                    const int n,          /* dim of the square matrix a */
                    const int *indx,      /* records the row pivoting */
                    double *b)
{
    int i, ii = -1, ip, j;
    double sum;

    for (i = 0; i < n; i ++) {
        ip = indx[i];
        sum = b[ip];
        b[ip] = b[i];
        if (ii != -1)
        {
            for (j= ii; j <= i - 1; j++) sum -= a[i*n+j]*b[j];
        }
        else
        {
            if (sum) ii = i;
        }
        b[i] = sum;
    }
    for (i = n-1; i >= 0; i --) {
        sum = b[i];
        for (j= i + 1; j < n; j++) sum -= a[i*n+j]*b[j];
        b[i] = sum/a[i*n+i];
    }
}
