Require Import VST.floyd.proofauto.
Require Import Reals.
Require Import vcfloat.FPCompCert.
Require Import twice.

#[export] Existing Instance NullExtension.Espec.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope float64_scope. 

(* If you don't open the scope, you have to do things like
  Float.of_int (Int.repr 2) *)
Definition Twice (x : ftype Tdouble) : ftype Tdouble := Float.mul 2.0 x.

Definition twice_spec :=
 DECLARE _twice
 WITH  x : ftype Tdouble
 PRE [ tdouble ] PROP() PARAMS(Vfloat x) SEP()
 POST [ tdouble ] PROP() RETURN (Vfloat (Twice x)) SEP().

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]
       PROP() RETURN (Vint (Int.repr 0)) SEP(TT).

Definition Gprog : funspecs := [twice_spec; main_spec].

Lemma body_twice: semax_body Vprog Gprog f_twice twice_spec.
Proof.
start_function.
forward.
(* I got this far on my own...
   thanks to Shant for figuring out the rest of this *)
apply prop_right_emp.
unfold Twice.
do 2 f_equal.
vm_compute.
apply B754_finite_ext.  
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward_call.
forward.
Qed.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
  prove_semax_prog.
  semax_func_cons body_twice.
  semax_func_cons body_main.
Qed.