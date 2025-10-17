/* Filename : matmul.c
   Author   : Stephen F. Siegel
   Created  : 2025-04-18
   Modified : 2025-04-21

   Matrix multiplication.

   frama-c -wp -wp-rte -wp-prover "alt-ergo,cvc4,z3,cvc5" \
   -wp-timeout 10 matmul.c

   Note: CVC5 is necessary (else 2 goals cannot be proved).

   matmul.c © 2025 by Stephen F. Siegel is licensed under CC BY 4.0.
   To view a copy of this license, visit
   https://creativecommons.org/licenses/by/4.0/
 */
#include <limits.h>

typedef struct Matrix {
  int nrow, ncol;
  int ** data;
} Matrix;

/*@
  predicate read2d(integer n, integer m, int ** a) =
    n>=0 && m>=0 &&
    \valid_read(a+(0..(n-1))) &&
    \valid_read(a[0..(n-1)]+(0..(m-1))) &&
    \forall integer i1,i2; (0<=i1<n && 0<=i2<n && i1!=i2) ==>
      \separated(a+(0..(n-1)), a[i1]+(0..(m-1)), a[i2]+(0..(m-1)));

  predicate Mat_valid_read(Matrix A) = read2d(A.nrow, A.ncol, A.data);

  predicate write2d(integer n, integer m, int ** a) =
    n>=0 && m>=0 &&
    \valid_read(a+(0..(n-1))) &&
    \valid(a[0..(n-1)]+(0..(m-1))) &&
    \forall integer i1,i2; (0<=i1<n && 0<=i2<n && i1!=i2) ==>
      \separated(a+(0..(n-1)), a[i1]+(0..(m-1)), a[i2]+(0..(m-1)));

  predicate Mat_valid(Matrix A) = write2d(A.nrow, A.ncol, A.data);

  predicate Mat_StructUnchanged{K,L}(Matrix mat) =
    \forall integer i; 0<=i<mat.nrow ==>
      \at(mat.data[i],K)==\at(mat.data[i],L);

  predicate Mat_Unchanged{K,L}(Matrix mat, integer rowBound) =
    Mat_StructUnchanged{K,L}(mat) &&
    \forall integer i,j; (0<=i<rowBound && 0<=j<mat.ncol) ==>
      \at(mat.data[i][j],K)==\at(mat.data[i][j],L);

  predicate Mat_Unchanged{K,L}(Matrix mat) =
    Mat_Unchanged{K,L}(mat, mat.nrow);

  predicate Sep(integer n1, integer m1, int ** a1,
                integer n2, integer m2, int ** a2) =
    \separated(a1+(0..(n1-1)), a2+(0..(n2-1)),
               a1[0..(n1-1)]+(0..(m1-1)), a2[0..(n2-1)]+(0..(m2-1)));

  predicate Mat_Sep(Matrix A, Matrix B) =
    Sep(A.nrow, A.ncol, A.data, B.nrow, B.ncol, B.data);

  logic integer
  Mat_Dot(Matrix A, integer row, Matrix B, integer col, integer n) =
    n<=0 ? 0 :
    Mat_Dot(A, row, B, col, n-1) + A.data[row][n-1]*B.data[n-1][col];

  logic integer
  Mat_Dot(Matrix A, integer row, Matrix B, integer col) =
    Mat_Dot(A, row, B, col, A.ncol);

  predicate
  Mat_DotBound1(Matrix A, integer row, Matrix B, integer col, integer n) =
    INT_MIN <= Mat_Dot(A, row, B, col, n) <= INT_MAX;

  predicate
  Mat_DotBound2(Matrix A, integer row, Matrix B, integer col, integer i) =
    INT_MIN <= A.data[row][i]*B.data[i][col] <= INT_MAX;

  predicate
  Mat_DotBound1(Matrix A, Matrix B) =
   \forall integer k1; 0<=k1<=A.ncol ==>
     (\forall integer row, col; (0<=row<A.nrow && 0<=col<B.ncol) ==>
      INT_MIN <= Mat_Dot(A, row, B, col, k1) <= INT_MAX);

  predicate
  Mat_DotBound2(Matrix A, Matrix B) =
    \forall integer k1; 0<=k1<A.ncol ==>
      (\forall integer row, col; (0<=row<A.nrow && 0<=col<B.ncol) ==>
       INT_MIN <= A.data[row][k1]*B.data[k1][col] <= INT_MAX);

  predicate
  Mat_DotBound(Matrix A, Matrix B) =
    Mat_DotBound1(A,B) && Mat_DotBound2(A,B);

  lemma Mat_DotInit:
    \forall Matrix A, B, integer row, col;
      (Mat_valid_read(A) && Mat_valid_read(B) && A.ncol==B.nrow &&
        0<=row<A.nrow && 0<=col<B.ncol) ==>
      Mat_Dot(A, row, B, col, 0) == 0;
    
  lemma Mat_DotInduct:
    \forall Matrix A, B, integer row, col, n;
      (Mat_valid_read(A) && Mat_valid_read(B) && A.ncol==B.nrow &&
        0<=row<A.nrow && 0<=col<B.ncol && 0<=n<A.ncol) ==>
      Mat_Dot(A, row, B, col, n+1) == Mat_Dot(A, row, B, col, n) +
        A.data[row][n]*B.data[n][col];

  predicate
  Mat_Mul(Matrix A, integer row, Matrix B, integer colBound, Matrix C) =
    \forall integer j; 0<=j<colBound ==>
      C.data[row][j] == Mat_Dot(A,row,B,j);

  predicate
  Mat_Mul(Matrix A, integer rowBound, Matrix B, Matrix C) =
    \forall integer i,j; (0<=i<rowBound && 0<=j<B.ncol) ==>
      C.data[i][j] == Mat_Dot(A,i,B,j);

  predicate
  Mat_Mul(Matrix A, Matrix B, Matrix C) = Mat_Mul(A, A.nrow, B, C);
*/

// inner product of row and column
/*@ requires Mat_valid_read(A) && Mat_valid_read(B);
  @ requires 0<=row<A.nrow && 0<=col<B.ncol;
  @ requires A.ncol == B.nrow;
  @ requires \forall integer n; 0<=n<=A.ncol ==> Mat_DotBound1(A,row,B,col,n);
  @ requires \forall integer i; 0<=i<A.ncol ==> Mat_DotBound2(A,row,B,col,i);
  @ ensures \result == Mat_Dot(A, row, B, col);
  @ assigns \nothing;
  @*/
int dot(Matrix A, int row, Matrix B, int col) {
  int result = 0;
  int n = A.ncol;
  /*@ loop invariant 0<=i<=n;
    @ loop invariant result == Mat_Dot(A, row, B, col, i);
    @ loop assigns i, result;
    @ loop variant n-i;
    @*/
  for (int i=0; i<n; i++)
    result += A.data[row][i]*B.data[i][col];
  return result;
}

/*@
  requires Mat_valid_read(A) && Mat_valid_read(B) && Mat_valid(C);
  requires Mat_Sep(A,C) && Mat_Sep(B,C);
  requires A.ncol==B.nrow && A.nrow==C.nrow && B.ncol==C.ncol;
  requires Mat_DotBound(A,B);
  ensures Mat_Mul(A,B,C);
  ensures Mat_Unchanged{Pre,Post}(A) && Mat_Unchanged{Pre,Post}(B);
  assigns C.data[0..(C.nrow-1)][0..(C.ncol-1)];
 */
void mul(Matrix A, Matrix B, Matrix C) {
  int n=A.nrow, m=B.ncol;
  /*@
    loop invariant 0<=i<=n;
    loop invariant outer_un: Mat_Unchanged{Pre,Here}(A) &&
       Mat_Unchanged{Pre,Here}(B);
    loop invariant outer_bound: Mat_DotBound(A,B);
    loop invariant outer_sep: Mat_Sep(A,C) && Mat_Sep(B,C);
    loop invariant outer_mul1: Mat_Mul(A, i, B, C);
    loop assigns i, C.data[0..(n-1)][0..(m-1)];
    loop variant n-i;
   */
  for (int i=0; i<n; i++)
    /*@
      loop invariant 0<=j<=m;
      loop invariant inner_un: Mat_Unchanged{Pre,Here}(A) &&
        Mat_Unchanged{Pre,Here}(B);
      loop invariant inner_C: Mat_Unchanged{LoopEntry,Here}(C,i);
      // for some reason, using Mat_DotBound(A,B) here doesn't work:
      loop invariant inner_bound: Mat_DotBound1(A,B) && Mat_DotBound2(A,B);
      loop invariant inner_sep: Mat_Sep(A,C) && Mat_Sep(B,C);
      loop invariant inner_mul1: Mat_Mul(A, i, B, C);
      loop invariant inner_mul2: Mat_Mul(A, i, B, j, C);
      loop assigns j, C.data[i][0..(m-1)];
      loop variant m-j;
     */
    for (int j=0; j<m; j++) {
    L:
      C.data[i][j] = dot(A, i, B, j);
      /*@ ghost
				/@
				loop invariant 0<=k<=A.ncol;
				loop invariant aux1: \forall integer row, col, k1;
			  	k1<=k && 0<=row<n && 0<=col<m ==>
				  Mat_Dot(A,row,B,col,k1) == \at(Mat_Dot(A,row,B,col,k1),L);
				loop assigns k;
				loop variant A.ncol-k;
				@/
				for (int k=0; k<A.ncol; k++) ;
      */
    }
}
