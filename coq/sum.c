/*@ requires \valid_read(x);
  @ requires \is_finite(x); forall 0<=i<=n;
  @ requires 0.0 <= k <= DBL_MAX / (double) (n+1);
  @ requires -k <= x[i] <= k forall i, k
  @ let true_acc = real_sum(x);
  @ ensures \fp_error(acc, true_acc) <= n*k*eps;
 */
double sum (double *x, int n, double k)
{
  int i;
  double acc = 0.0;
  for (i = 0; i < n; i++) {
    acc += x[i];
  }
  return acc;
}

