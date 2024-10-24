#ifndef QUATERNION_MATH_
#define QUATERNION_MATH_

#include "Matrix_Algebra.h"

#ifdef __cplusplus
extern "C"{
#endif

typedef Vector_4 Quaternion;

void qvqi(Quaternion* q, Vector_3* v, Vector_3* vo);
void qivq(Quaternion* q, Vector_3* v, Vector_3* vo);

void q2v(Quaternion* q, Vector_3* v);
void v2q(Vector_3* v, Quaternion* q);

void q2dcm(Quaternion* q, Matrix_3x3* dcm);
void dcm2q(Matrix_3x3* dcm, Quaternion* q);

void qq(Quaternion* a, Quaternion* b, Quaternion* c);
void qiq(Quaternion* a, Quaternion* b, Quaternion* c);
void qqi(Quaternion* a, Quaternion* b, Quaternion* c);
void qiqi(Quaternion* a, Quaternion* b, Quaternion* c);

#ifdef __cplusplus
}
#endif
#endif
