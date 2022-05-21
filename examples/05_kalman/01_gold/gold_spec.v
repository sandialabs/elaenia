Require Import VST.floyd.proofauto.
Require Import gold_2.
Declare Scope float32_scope.
Delimit Scope float32_scope with F32.
Declare Scope float64_scope.
Delimit Scope float64_scope with F64.

Notation "x + y" := (Float32.add x y) (at level 50, left associativity) : float32_scope.
Notation "x - y"  := (Float32.sub x y) (at level 50, left associativity) : float32_scope.
Notation "x * y"  := (Float32.mul x y) (at level 40, left associativity) : float32_scope.
Notation "x / y"  := (Float32.div x y) (at level 40, left associativity) : float32_scope.
Notation "- x" := (Float32.neg x) (at level 35, right associativity) : float32_scope.

Notation "x <= y" := (Float32.cmp Cle x y = true) (at level 70, no associativity) : float32_scope.
Notation "x < y" := (Float32.cmp Clt x y = true) (at level 70, no associativity) : float32_scope.
Notation "x >= y" := (Float32.cmp Cge x y = true) (at level 70, no associativity) : float32_scope.
Notation "x > y" := (Float32.cmp Cgt x y = true) (at level 70, no associativity) : float32_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x <= y < z" := (x <= y /\ y < z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x < y < z" := (x < y /\ y < z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x < y <= z" := (x < y /\ y <= z)%F32 (at level 70, y at next level) : float32_scope.

Notation "x + y" := (Float.add x y) (at level 50, left associativity) : float64_scope.
Notation "x - y"  := (Float.sub x y) (at level 50, left associativity) : float64_scope.
Notation "x * y"  := (Float.mul x y) (at level 40, left associativity) : float64_scope.
Notation "x / y"  := (Float.div x y) (at level 40, left associativity) : float64_scope.
Notation "- x" := (Float.neg x) (at level 35, right associativity) : float64_scope.

Notation "x <= y" := (Float.cmp Cle x y = true) (at level 70, no associativity) : float64_scope.
Notation "x < y" := (Float.cmp Clt x y = true) (at level 70, no associativity) : float64_scope.
Notation "x >= y" := (Float.cmp Cge x y = true) (at level 70, no associativity) : float64_scope.
Notation "x > y" := (Float.cmp Cgt x y = true) (at level 70, no associativity) : float64_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x <= y < z" := (x <= y /\ y < z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x < y < z" := (x < y /\ y < z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x < y <= z" := (x < y /\ y <= z)%F64 (at level 70, y at next level) : float64_scope.


Definition update_p (K p : float) : float :=
  ((Float.of_int (Int.repr 1) - K) * p)%F64.
Definition update_state (K x m : float) : float := (x + K * (m - x))%F64.
Definition update_gain (p r : float) : float := (p / (p + r))%F64.

Definition update_p_spec : ident * funspec :=
DECLARE _update_p
 WITH Kval : float, pval : float
 PRE [tdouble, tdouble]
 PROP ()
 PARAMS (Vfloat Kval; Vfloat pval)
 SEP ()
 POST [tdouble]
 EX ret : float,
 PROP (ret = update_p Kval pval)
 RETURN (Vfloat ret)
 SEP ().

Definition update_state_spec : ident * funspec :=
DECLARE _update_state
 WITH Kval : float, xval : float, mval : float
 PRE [tdouble, tdouble, tdouble]
 PROP ()
 PARAMS (Vfloat Kval; Vfloat xval; Vfloat mval)
 SEP ()
 POST [tdouble]
 EX ret : float,
 PROP (ret = update_state Kval xval mval)
 RETURN (Vfloat ret)
 SEP ().

Definition update_gain_spec : ident * funspec :=
DECLARE _update_gain
 WITH pval : float, rval : float
 PRE [tdouble, tdouble]
 PROP ()
 PARAMS (Vfloat pval; Vfloat rval)
 SEP ()
 POST [tdouble]
 EX ret : float,
 PROP (ret = update_gain pval rval)
 RETURN (Vfloat ret)
 SEP ().

Definition main_spec : ident * funspec :=
DECLARE _main
 WITH gv : globals
 PRE [] main_pre prog tt gv
 POST [tint]
 EX ret : int,
 PROP (ret = (Int.repr 0))
 RETURN (Vint ret)
 SEP (TT).
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* This is an extremely shallow interpretation of the printf function.
 Actual analysis of the printf function is beyond the scope of this project
 at the moment.
Definition printf_spec : ident * funspec :=
DECLARE _printf
 WITH str : val, sl : list byte, sh : share
 PRE [tptr tschar]
 PROP (readable_share sh)
 PARAMS (str)
 SEP (cstring sh sl str)
 POST [tint]
 EX ret : int,
 PROP (ret = (Int.repr (Zlength sl)))
 RETURN (Vint ret)
 SEP (cstring sh sl str).
*)

Definition Gprog := [update_p_spec; update_state_spec; update_gain_spec; main_spec].                                      
Transparent Float.of_bits Float.of_int IEEE754_extra.BofZ.

Lemma body_update_p : semax_body Vprog Gprog f_update_p update_p_spec.
Proof.
  start_function.
  forward.
  Exists (update_p Kval pval).
  unfold update_p.
  entailer!; repeat f_equal.
  unfold Float.of_bits, Float.of_int, IEEE754_extra.BofZ, Binary.binary_normalize,
      Bits.b64_of_bits, Binary.binary_round, Bits.binary_float_of_bits.
  apply Binary.B2FF_inj; reflexivity.
Qed.

Lemma body_update_state : semax_body Vprog Gprog f_update_state update_state_spec.
Proof.
  start_function.
  forward.
  Exists (update_state Kval xval mval).
  entailer!.
Qed.

Lemma body_update_gain : semax_body Vprog Gprog f_update_gain update_gain_spec.
Proof.
  start_function.
  forward.
  Exists (update_gain pval rval).
  entailer!.
Qed.

Definition sensor_data : list Z :=
      [4652244803352788992; 4651910551817945088; 4652156842422566912;
       4652086473678389248; 4652121658050478080; 4651822590887723008;
       4652077677585367040; 4652297579910922240; 4652112861957455872;
       4652104065864433664].

(*
  Vfloat (Float.of_bits (Int64.repr 4636737291354636288)) = 
  Vfloat
    (update_p
       (update_gain (Float.of_bits (Int64.repr 4636737291354636288))
          (Float.of_bits (Int64.repr 4642120500284227584)))
       (Float.of_bits (Int64.repr 4636737291354636288))) /\
  Vfloat (Float.of_bits (Int64.repr 4651919347910967296)) = 
  Vfloat
    (update_state
       (update_gain (Float.of_bits (Int64.repr 4636737291354636288))
          (Float.of_bits (Int64.repr 4642120500284227584)))
       (Float.of_bits (Int64.repr 4651919347910967296))
       (Float.of_bits (Int64.repr (Znth i sensor_data))))
 *)

Definition main_loop_body (i : nat) (r_var p_var curr : float) : (float * float) :=
  let input := nth i sensor_data default in
  let K := update_gain p_var r_var in
  let curr := update_state K curr (Float.of_bits (Int64.repr input)) in
  let p_var := update_p K p_var in
  (p_var, curr).

Definition main_loop (k : nat) (r_var p_var curr : float) : (float * float) :=
  fold_left (fun acc i => main_loop_body i r_var (fst acc) (snd acc)) (seq 0 k) (p_var, curr).
Definition r_var : float := Float.of_bits (Int64.repr 4642120500284227584).
Definition p_var_init : float := Float.of_bits (Int64.repr 4636737291354636288).
Definition curr_init : float := Float.of_bits (Int64.repr 4651919347910967296).

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  repeat forward.
  forward_for_simple_bound
    10
    (EX i: Z,
        (PROP (0 <= i <= 10)
              LOCAL(temp _r_var (Vfloat r_var);
                    temp _p_var (Vfloat (fst (main_loop (Z.to_nat i) r_var p_var_init curr_init)));
                    temp _curr (Vfloat (snd (main_loop (Z.to_nat i) r_var p_var_init curr_init)));
                    lvar _sensor_data (tarray tdouble 10) v_sensor_data; 
                    gvars gv)
              SEP((data_at Tsh (tarray tdouble 10) (map (fun y => (Vfloat (Float.of_bits (Int64.repr y)))) sensor_data)
                           v_sensor_data);
                   has_ext tt)
          )
    ).
  - entailer!.
  - forward.
    repeat (forward_call; let vret := fresh "vret" in Intros vret).
    forward.
    entailer!.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    unfold main_loop, main_loop_body.
    rewrite seq_S, Nat.add_0_l, fold_left_app; split; cbn [fold_left fst snd]; auto.
    rewrite nth_Znth', Z2Nat_id'.
    replace (Z.max 0 i) with i by lia.
    reflexivity.
  - forward.
    EExists; entailer!.
Qed.
