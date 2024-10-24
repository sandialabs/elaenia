#include <math.h>
#include <stdio.h>

#include "Matrix_Algebra.h"

static void Matrix_Error(const char* msg) {
  printf("%s", msg);
}

void axb(const Matrix_MxN* a, const Matrix_MxN* b, Matrix_MxN* C) {

  int r, c, i;
  //if this is not done, compcert inserts a 400 line long init
  //of the array, here we are simulating this instead as 
  //not initializing the array leads to problems in the final copy
  #ifdef __COMPCERT__
  Matrix_MxN ret;
  for (int j = 0; j < MAX_N; j++)
    for (int k = 0; k < MAX_N; k ++)
      ret.a[j][k] = 0.0;
  ret.m = a->m;
  ret.n = b->n;
  #else
  Matrix_MxN ret = {a->m, b->n};
  #endif

  if (a->n != b->m) {
    Matrix_Error("matrix_multiply - size error axb\n");
  }

  for (r=0; r<a->m; r++) {
    for (c=0; c<b->n; c++) {
      ret.a[r][c] = 0.0; // Caching not supported in CompCert?
      for (i=0; i<a->n; i++) ret.a[r][c] += a->a[r][i]*b->a[i][c];
    }
  }
  #ifdef __COMPCERT__
  C->m = ret.m;
  C->n = ret.n;
  for (int j = 0; j < MAX_N; j++)
    for (int k = 0; k < MAX_N; k++)
      C->a[j][k] = ret.a[j][k];
  #else
  *C = ret;
  #endif
  
}

void lu_bksb(
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
        if (ii != -1) {
            for (j= ii; j <= i - 1; j++) sum -= a[i*n+j]*b[j];
        }
        else {
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

void lu_dcmp(
                    double *a,      /* matrix that is replaced with its LU Decomp */
                    const int n,    /* dim of the square matrix a */
                    int *indx,      /* records the row pivoting */
                    float *d)       /* +1/-1 if even/odd number of row interchanges */
{
    int i, imax, j, k;
    double big, dum, sum, temp;
    double vv[MAX_N];

    *d = (float)1.0;                /* no row interchanges yet */

    for (i = 0; i < n; i++){        /* loop rows to get scaling info */
        big = 0.0;
        for (j = 0; j < n; j++)
        {
            if ((temp = fabs(a[i*n+j])) > big) {
                 big = temp;
            }
        }
        if (big == 0.0) { // Not a sufficient condition to safely divide
                /*This should NEVER happen in real-time operation, but just in*/
                /* case, set to something tiny*/
                big = -1e99;
				Matrix_Error("Singular matrix in function lu_dcmp.\n");
				while(-1);
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
            if ( (dum = vv[i]*fabs(sum)) >= big ) {
                big = dum;
                imax = i;
            }
        }

        if (j != imax) {            /* interchange rows if necessary */
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
        if (j != (n-1)) {
            dum = 1.0/(a[j*n+j]);
            for (i = j + 1; i < n; i++) a[i*n+j] *= dum;
        }
    }
}

