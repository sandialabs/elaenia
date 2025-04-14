/* Assume a, b, c has length 4, corresponding to
 * (0,1,2,3) = (s, i, j, k)
 */
/* Multiply quaternions */
void qq(const double* a, const double* b, double* c) {
  double q[4];

  q[0] = a[0] * b[0] - a[1] * b[1] - a[2] * b[2] - a[3] * b[3];
  q[1] = a[1] * b[0] + a[0] * b[1] - a[3] * b[2] + a[2] * b[3];
  q[2] = a[2] * b[0] + a[3] * b[1] + a[0] * b[2] - a[1] * b[3];
  q[3] = a[3] * b[0] - a[2] * b[1] + a[1] * b[2] + a[0] * b[3];
}

