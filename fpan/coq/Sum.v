Require Import Coq.Unicode.Utf8.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Reals.Reals.
Require Import Flocq.Core.Core.
Require Import Flocq.IEEE754.Bits.

Open Scope R_scope.

Theorem sterbenz :
  ∀ (beta : radix) (fexp : Z → Z),
  Valid_exp fexp → Monotone_exp fexp →
  ∀ x y : R,
  generic_format beta fexp x → generic_format beta fexp y →
  (y / 2 <= x <= 2 * y)%R →
  generic_format beta fexp (x - y).
Proof.
  Admitted.


(* May be easiest to get VCs from Frama-C from this C function.

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

double x = {0.0, 0.1, 0.2, 0.3, ...};
double s = sum(x);
*)


Definition u = machine_eps/2.
  
Notation "| _ |" = abs.

Theorem sum_error :
  ∀ (n : nat) (x : vec n binary32),
  | sum x - float (sum x) | <= n * u * max x.

Definition γ (n : nat) : R := 

Theorem inner_product_error :
   ∀ (n : nat) (x y : vec n binary32),
   | x . y - float(x . y)| <= γ n |x| * |y| + n * (δ/2 (1 + γ (n-1))).
