/* 3x3 matrix multiplication */
/* assume a, b, c have length 9, row-major order */
void axb_33(const double* a, const double* b, double* C)
{
  C[0] = a[0]*b[0] + a[1]*b[3] + a[2]*b[6];
  C[1] = a[0]*b[1] + a[1]*b[4] + a[2]*b[7];
  C[2] = a[0]*b[2] + a[1]*b[5] + a[2]*b[8];

  C[3] = a[3]*b[0] + a[4]*b[3] + a[5]*b[6];
  C[4] = a[3]*b[1] + a[4]*b[4] + a[5]*b[7];
  C[5] = a[3]*b[2] + a[4]*b[5] + a[5]*b[8];

  C[6] = a[6]*b[0] + a[7]*b[3] + a[8]*b[6];
  C[7] = a[6]*b[1] + a[7]*b[4] + a[8]*b[7];
  C[8] = a[6]*b[2] + a[7]*b[5] + a[8]*b[8];
}

