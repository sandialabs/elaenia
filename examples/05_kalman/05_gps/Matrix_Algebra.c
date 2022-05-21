#include "Matrix_Algebra.h"

void a_add_b_33(const Matrix_3x3* a, const Matrix_3x3* b, Matrix_3x3* C) {
  Matrix_3x3 ret = {{{0}}, NULL};
  int r, c;
  for (r=0; r<3; r++) {
    for (c=0; c<3; c++) {
      ret.a[r][c] = a->a[r][c] + b->a[r][c];
    }
  }

  *C = ret;
}

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

void diag_33(const Vector_3* v, Matrix_3x3* a) {

  memset(a, 0, 9*sizeof(double));
  a->s._11 = v->v.i;
  a->s._22 = v->v.j;
  a->s._33 = v->v.k;

}

