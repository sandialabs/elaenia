Require Import VST.floyd.proofauto.
Require Import Reals.
Require Import vcfloat.FPCompCert.
Require Import twice.

#[export] Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
  prove_semax_prog.
  semax_func_cons body_force.
  semax_func_cons body_lfstep.
  semax_func_cons body_integrate.
  semax_func_cons body_main.
Qed.