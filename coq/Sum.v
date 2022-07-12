Require Import Coq.Unicode.Utf8.
Require Import Flocq.Core.Core.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Reals.Reals.
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
