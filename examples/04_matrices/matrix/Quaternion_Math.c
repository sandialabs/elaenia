#include <math.h>

#include "Matrix_Algebra.h"
#include "Quaternion_Math.h"



void qq(Quaternion* a, Quaternion* b, Quaternion* c) {
  Quaternion q;

  q.v.s = a->v.s * b->v.s - a->v.i * b->v.i - a->v.j * b->v.j - a->v.k * b->v.k;
  q.v.i = a->v.i * b->v.s + a->v.s * b->v.i - a->v.k * b->v.j + a->v.j * b->v.k;
  q.v.j = a->v.j * b->v.s + a->v.k * b->v.i + a->v.s * b->v.j - a->v.i * b->v.k;
  q.v.k = a->v.k * b->v.s - a->v.j * b->v.i + a->v.i * b->v.j + a->v.s * b->v.k;
  *c = q;
}


void qiq(Quaternion* a, Quaternion* b, Quaternion* c) {
  Quaternion q;

  q.v.s = a->v.s * b->v.s + a->v.i * b->v.i + a->v.j * b->v.j + a->v.k * b->v.k;
  q.v.i =-a->v.i * b->v.s + a->v.s * b->v.i + a->v.k * b->v.j - a->v.j * b->v.k;
  q.v.j =-a->v.j * b->v.s - a->v.k * b->v.i + a->v.s * b->v.j + a->v.i * b->v.k;
  q.v.k =-a->v.k * b->v.s + a->v.j * b->v.i - a->v.i * b->v.j + a->v.s * b->v.k;
  *c = q;
}


void qqi(Quaternion* a, Quaternion* b, Quaternion* c) {
  Quaternion q;

  q.v.s = a->v.s * b->v.s + a->v.i * b->v.i + a->v.j * b->v.j + a->v.k * b->v.k;
  q.v.i = a->v.i * b->v.s - a->v.s * b->v.i + a->v.k * b->v.j - a->v.j * b->v.k;
  q.v.j = a->v.j * b->v.s - a->v.k * b->v.i - a->v.s * b->v.j + a->v.i * b->v.k;
  q.v.k = a->v.k * b->v.s + a->v.j * b->v.i - a->v.i * b->v.j - a->v.s * b->v.k;
  *c = q;
}


void qiqi(Quaternion* a, Quaternion* b, Quaternion* c) {
}


void qvqi(Quaternion* q, Vector_3* v, Vector_3* vo) {

  double t0, t1, t2, t3;

  t0 = -q->v.i*v->v.i - q->v.j*v->v.j - q->v.k*v->v.k;
  t1 =  q->v.s*v->v.i - q->v.k*v->v.j + q->v.j*v->v.k;
  t2 =  q->v.k*v->v.i + q->v.s*v->v.j - q->v.i*v->v.k;
  t3 = -q->v.j*v->v.i + q->v.i*v->v.j + q->v.s*v->v.k;

  vo->v.i = -q->v.i*t0 + q->v.s*t1 - q->v.k*t2 + q->v.j*t3;
  vo->v.j = -q->v.j*t0 + q->v.k*t1 + q->v.s*t2 - q->v.i*t3;
  vo->v.k = -q->v.k*t0 - q->v.j*t1 + q->v.i*t2 + q->v.s*t3;

}


void qivq(Quaternion* q, Vector_3* v, Vector_3* vo) {
  double t0, t1, t2, t3;
  
  t0 =  q->v.i*v->v.i + q->v.j*v->v.j + q->v.k*v->v.k;
  t1 =  q->v.s*v->v.i + q->v.k*v->v.j - q->v.j*v->v.k;
  t2 = -q->v.k*v->v.i + q->v.s*v->v.j + q->v.i*v->v.k;
  t3 =  q->v.j*v->v.i - q->v.i*v->v.j + q->v.s*v->v.k;

  vo->v.i = q->v.i*t0 + q->v.s*t1 + q->v.k*t2 - q->v.j*t3;
  vo->v.j = q->v.j*t0 - q->v.k*t1 + q->v.s*t2 + q->v.i*t3;
  vo->v.k = q->v.k*t0 + q->v.j*t1 - q->v.i*t2 + q->v.s*t3;
}


void q2v(Quaternion* q, Vector_3* v) {
  double th, d, th2, sgn;

  /* calculate theta */
  sgn = (q->v.s < 0. ? -1. : 1.);
  d = sqrt(q->v.i*q->v.i + q->v.j*q->v.j + q->v.k*q->v.k);
  th = 2.*atan2(d, sgn*q->v.s);

  /* make sure we dont get a division by zero */
  if (fabs(th) < 1.e-6) {
    th2 = th*th;
    d = 2./(1. - th2*(1./24. - th2*(1./1920. - th2/322560.)));
  }
  else  d = th/sin(th/2.);

  /* calculate the rotation vector */
  v->v.i = sgn*q->v.i*d;
  v->v.j = sgn*q->v.j*d;
  v->v.k = sgn*q->v.k*d;
}


void v2q(Vector_3* v, Quaternion* q) {
  double norm, d, th2;

  /* calculate the norm of the vector */
  norm = norm_3(v);

  /* if the norm is small, then calculate using a Taylor expansion */
  if (norm < 1.e-6) {
    th2 = norm*norm;
    d = (1. - th2*(1./24. - th2*(1./1920. - th2/322560.)))/2.;
  }
  else d = sin(norm/2.)/norm;

  /* calculate the quaternion */
  q->v.s = cos(norm/2.);
  q->v.i = v->v.i*d;
  q->v.j = v->v.j*d;
  q->v.k = v->v.k*d;
}


void q2dcm(Quaternion* q, Matrix_3x3* dcm) {

  Quaternion q_u;
  double xx, xy, xz, xs, yy, yz, ys, zz, zs, ss;
  unit_4(q, &q_u);

  xx = q_u.v.i * q_u.v.i;
  xy = q_u.v.i * q_u.v.j;
  xz = q_u.v.i * q_u.v.k;
  xs = q_u.v.i * q_u.v.s;

  yy = q_u.v.j * q_u.v.j;
  yz = q_u.v.j * q_u.v.k;
  ys = q_u.v.j * q_u.v.s;

  zz = q_u.v.k * q_u.v.k;
  zs = q_u.v.k * q_u.v.s;

  ss = q_u.v.s * q_u.v.s;

  dcm->s._11 = ss+xx-yy-zz;  dcm->s._12 = 2*(xy - zs);  dcm->s._13 = 2*(xz + ys);
  dcm->s._21 = 2*(xy + zs);  dcm->s._22 = ss-xx+yy-zz;  dcm->s._23 = 2*(yz - xs);
  dcm->s._31 = 2*(xz - ys);  dcm->s._32 = 2*(yz + xs);  dcm->s._33 = ss-xx-yy+zz;

}


void dcm2q(Matrix_3x3* dcm, Quaternion* q) {
  Matrix_3x3* A = dcm;
  double Tr = A->s._11 + A->s._22 + A->s._33;
  double Ps = 1+Tr;
  double Px = 1+2*A->s._11-Tr;
  double Py = 1+2*A->s._22-Tr;
  double Pz = 1+2*A->s._33-Tr;

  double max = Ps;
  int mi = 1;

  if (Px > max) { max = Px; mi = 2; }
  if (Py > max) { max = Py; mi = 3; }
  if (Pz > max) { max = Pz; mi = 4; }

  switch (mi) {
  /* scalar is max */
  case 1:
    q->v.s = 0.5*sqrt(Ps);
    q->v.i = (A->s._32 - A->s._23) / (4*q->v.s);
    q->v.j = (A->s._13 - A->s._31) / (4*q->v.s);
    q->v.k = (A->s._21 - A->s._12) / (4*q->v.s);
    break;

  /* x is max */
  case 2:
    q->v.i = 0.5*sqrt(Px);
    q->v.j = (A->s._21 + A->s._12) / (4*q->v.i);
    q->v.k = (A->s._13 + A->s._31) / (4*q->v.i);
    q->v.s = (A->s._32 - A->s._23) / (4*q->v.i);
    break;

  /* y is max */
  case 3:
    q->v.j = 0.5*sqrt(Py);
    q->v.k = (A->s._32 + A->s._23) / (4*q->v.j);
    q->v.s = (A->s._13 - A->s._31) / (4*q->v.j);
    q->v.i = (A->s._21 + A->s._12) / (4*q->v.j);
    break;

  /* z is max */
  case 4:
    q->v.k = 0.5*sqrt(Pz);
    q->v.s = (A->s._21 - A->s._12) / (4*q->v.k);
    q->v.i = (A->s._13 + A->s._31) / (4*q->v.k);
    q->v.j = (A->s._32 + A->s._23) / (4*q->v.k);
    break;

  }

}
