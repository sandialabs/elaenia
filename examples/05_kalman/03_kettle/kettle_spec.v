Require Import VST.floyd.proofauto.
Require Import kettle2.
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


Definition update_p (K p p_del t q : float) : float :=
  ((Float.of_int (Int.repr 1) - K) * p + t*t*p_del + q)%F64.
Definition update_state (K x x_del t m : float) : float := (x + t * x_del + K * (m - x))%F64.
Definition update_p_del (p_del q : float) : float := (p_del + q)%F64.
Definition update_gain (p r : float) : float := (p / (p + r))%F64.


Definition update_p_spec : ident * funspec :=
DECLARE _update_p
 WITH Kval : float, pval : float, p_delval : float, tval : float, qval : float
 PRE [tdouble, tdouble, tdouble, tdouble, tdouble]
 PROP ()
 PARAMS (Vfloat Kval; Vfloat pval; Vfloat p_delval; Vfloat tval; Vfloat qval)
 SEP ()
 POST [tdouble]
 EX ret : float,
 PROP (ret = update_p Kval pval p_delval tval qval)
 RETURN (Vfloat ret)
 SEP ().

Definition update_state_spec : ident * funspec :=
DECLARE _update_state
 WITH Kval : float, xval : float, x_delval : float, tval: float, mval : float
 PRE [tdouble, tdouble, tdouble, tdouble, tdouble]
 PROP ()
 PARAMS (Vfloat Kval; Vfloat xval; Vfloat x_delval; Vfloat tval; Vfloat mval)
 SEP ()
 POST [tdouble]
 EX ret : float,
 PROP (ret = update_state Kval xval x_delval tval mval)
 RETURN (Vfloat ret)
 SEP ().

Definition update_p_del_spec : ident * funspec :=
DECLARE _update_p_del
 WITH p_delval : float, qval : float
 PRE [tdouble, tdouble]
 PROP ()
 PARAMS (Vfloat p_delval; Vfloat qval)
 SEP ()
 POST [tdouble]
 EX ret : float,
 PROP (ret = update_p_del p_delval qval)
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
(*

Definition print1_spec : ident * funspec :=
DECLARE _print1
 WITH v : val, rsh : share, sval : string, 
 PRE [tptr tchar]
 PROP (readable_share rsh; sval = List.map compcert_byte_of_byte (list_byte_of_string s)))
 PARAMS (v)
 SEP (
 POST [tint]
 EX ret : int,
 PROP (ret = (Int.repr 0))
 RETURN (Vint ret)
 SEP (TT).
*)      

Global Instance CompSpecs : compspecs. make_compspecs prog. Defined.
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

Definition Gprog := [update_p_spec; update_state_spec; update_p_del_spec; update_gain_spec; main_spec].
Transparent Float.of_bits Float.of_int IEEE754_extra.BofZ.

Lemma body_update_p : semax_body Vprog Gprog f_update_p update_p_spec.
Proof.
  start_function.
  forward.
  Exists (update_p Kval pval p_delval tval qval).
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
  Exists (update_state Kval xval x_delval tval mval).
  entailer!.
Qed.

Lemma body_update_p_del : semax_body Vprog Gprog f_update_p_del update_p_del_spec.
Proof.
  start_function.
  forward.
  Exists (update_p_del p_delval qval).
  entailer!.
Qed.

Lemma body_update_gain : semax_body Vprog Gprog f_update_gain update_gain_spec.
Proof.
  start_function.
  forward.
  Exists (update_gain pval rval).
  entailer!.
Qed.

Definition z_sensor_data : list Z :=
  [4626238274723328819; 4626421233458190746; 4626348049964245975; 4626615451192121098;
   4625700657517811466; 4626607006942819779; 4626956035913940992; 4627141809398570025;
   4627882088587319050; 4629027691742531420; 4629244427474598625; 4629216279976927560;
   4629943892791724605; 4630222553018668155].
Definition sensor_data : list float :=
  map (fun x => (Float.of_bits (Int64.repr x))) z_sensor_data.
(*
int main() {
  double m, K;
  double t         =   5.0; // Time between measurements
  double temp      =  16.0; // Initial guess temperature
  double rate      =   0.0; // Initial guess heating rate
  double p_var     = 100.0; // Estimation variance (10^2)
  double p_del_var =   0.0; // Estimation variance
  double r_var     =  16.0; // Measurement variance (4^2)
  double q         =   1.0; // Process variance noise (1^2)

  // TODO: Model as matrix
  printf("temperature\tp_var\tK\n");
  while(scanf("%lf", &m) != EOF) {
    K          = update_gain(p_var, r_var);
    temp       = update_state(K, m, rate, t, m);
    rate       = rate; // Constant heating rate
    p_var      = update_p(K, p_var, p_del_var, t, q);
    p_del_var  = update_p_del(p_del_var, 0.0);
    printf("%8.3lf\t%8.3lf\t%8.3lf\n", temp, p_var, K);
  }
input values: p_var r_var m rate t p_del_var q
ouput values: K temp rate p_var p_del_var
cycle uses : p_var p_del_var
*)

Definition main_loop_body (i : nat) (t temp rate p_var p_del_var r_var q : float) : (float * float * float) :=
  let m := nth i sensor_data default in
  let K := update_gain p_var r_var in
  let temp := update_state K m rate t m in
  let rate := rate in
  let p_var := update_p K p_var p_del_var t q in
  let p_del_var := update_p_del p_del_var (Float.of_int (Int.repr 0)) in
  (p_var, p_del_var, temp).

Definition main_loop (k : nat) (t temp rate p_var p_del_var r_var q : float) : (float * float * float) :=
  fold_left (fun acc i => main_loop_body i t (snd acc) rate (fst (fst acc)) (snd (fst acc)) r_var q)
            (seq 0 k) (p_var, p_del_var, temp).
Definition t_var : float := Float.of_bits (Int64.repr 4617315517961601024).
Definition temp_var : float := Float.of_bits (Int64.repr 4625196817309499392).
Definition rate_var : float := Float.of_bits (Int64.repr 0).
Definition p_var : float := Float.of_bits (Int64.repr 4636737291354636288).
Definition p_del_var : float := Float.of_bits (Int64.repr 0).
Definition r_var : float := Float.of_bits (Int64.repr 4625196817309499392).
Definition q_var : float := Float.of_bits (Int64.repr 4607182418800017408).

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  repeat forward.
  set (ml := fun k => main_loop k t_var temp_var rate_var p_var p_del_var r_var q_var).
  forward_for_simple_bound
    14
    (EX i: Z,
        (PROP (0 <= i <= 14)
              LOCAL(temp _q (Vfloat (Float.of_bits (Int64.repr 4607182418800017408)));
                    temp _r_var (Vfloat (Float.of_bits (Int64.repr 4625196817309499392)));
                    temp _p_del_var (Vfloat (snd (fst (ml (Z.to_nat i)))));
                    temp _p_var (Vfloat (fst (fst (ml (Z.to_nat i)))));
                    temp _rate (Vfloat (Float.of_bits (Int64.repr 0)));
                    temp _temp (Vfloat (snd (ml (Z.to_nat i))));
                    temp _t (Vfloat (Float.of_bits (Int64.repr 4617315517961601024)));
                    lvar _sensor_data (tarray tdouble 14) v_sensor_data; 
                    gvars gv)
              SEP((data_at Tsh (tarray tdouble 14) (map  Vfloat sensor_data)
                           v_sensor_data);
                   has_ext tt)
          )
    ).
  - entailer!.
  - forward.
    + entailer!.
      enough (forall m l, In m (map (fun x => (Vfloat (Float.of_bits (Int64.repr x)))) l) -> is_float m) as P
          by (apply (P _ z_sensor_data); apply Znth_In; cbn; auto).
      induction l; intros; [contradiction| cbn in H4; destruct H4; auto].
      rewrite <- H4; cbn; auto.
    + repeat (forward_call; let vret := fresh "vret" in Intros vret; try forward).
      entailer!.
      repeat split; f_equal; unfold ml; replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia;
        unfold main_loop, main_loop_body; rewrite seq_S, Nat.add_0_l, fold_left_app; cbn [fold_left fst snd]; auto.
        f_equal; rewrite nth_Znth', Z2Nat_id'; replace (Z.max 0 i) with i by lia; reflexivity.
  - forward.
    EExists; entailer!.
Qed.



Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Require Import Reals.


Section fidelity.

  Context {NANS : Nans}.
  Set Bullet Behavior "Strict Subproofs".

  Definition update_pR (K p p_del t q : R) : R := ((1 - K) * p + t*t*p_del + q)%R.
  Definition update_stateR (K x x_del t m : R) : R := (x + t * x_del + K * (m - x))%R.
  Definition update_p_delR (p_del q : R) : R := (p_del + q)%R.
  Definition update_gainR (p r : R) : R := (p / (p + r))%R.
  
  Definition update_pf (K p p_del t q : ftype Tdouble) : ftype Tdouble :=
    ((1 - K) * p + t*t*p_del + q)%F64.
  Definition update_statef (K x x_del t m : ftype Tdouble) : ftype Tdouble :=
    (x + t * x_del + K * (m - x))%F64.
  Definition update_p_delf (p_del q : ftype Tdouble) : ftype Tdouble :=
    (p_del + q)%F64.
  Definition update_gainf (p r : ftype Tdouble) : ftype Tdouble :=
    (p / (p + r))%F64.

  Definition _p_del_id : ident := 1%positive.
  Definition _q_id : ident := 2%positive.
  Definition _K_id : ident := 3%positive.
  Definition _t_id : ident := 4%positive.
  Definition _x_id : ident := 5%positive.
  Definition _x_del_id : ident := 6%positive.
  Definition _m_id : ident := 7%positive.
  Definition _r_id : ident := 8%positive.
  Definition _p_id : ident := 9%positive.
  
  Definition update_p_delf_expr := ltac:(let e' := 
                                           HO_reify_float_expr
                                             constr:([_p_del_id; _q_id])
                                                      update_p_delf
                                         in exact e').
  Definition update_state_expr := ltac:(let e' := 
                                          HO_reify_float_expr
                                            constr:([_K_id; _x_id; _x_del_id; _t_id; _m_id])
                                                     update_statef
                                        in exact e').
  Definition update_p_expr := ltac:(let e' := 
                                      HO_reify_float_expr
                                        constr:([_K_id; _p_id; _p_del_id; _t_id; _q_id])
                                                 update_pf
                                    in exact e').
  Definition update_gain_expr := ltac:(let e' := 
                                         HO_reify_float_expr
                                           constr:([_p_id; _r_id])
                                                    update_gainf
                                       in exact e').
  
  Definition varinfo_p_del := Build_varinfo Tdouble _p_del_id (-100) 100.
  Definition varinfo_q := Build_varinfo Tdouble _q_id (-1000) 1000.
  Definition varinfo_K := Build_varinfo Tdouble _K_id (-1000) 1000.
  Definition varinfo_t := Build_varinfo Tdouble _t_id (-1000) 1000.
  Definition varinfo_x := Build_varinfo Tdouble _x_id (-1000) 1000.
  Definition varinfo_x_del := Build_varinfo Tdouble _x_del_id (-1000) 1000.
  Definition varinfo_m := Build_varinfo Tdouble _m_id (-1000) 1000.
  Definition varinfo_r := Build_varinfo Tdouble _r_id 1 1000.
  Definition varinfo_p := Build_varinfo Tdouble _p_id 1 1000.
  
  Lemma update_p_del_var (fp_del fq : ftype Tdouble) :
    let vm := ltac:(let z := compute_PTree (valmap_of_list
                                              [(_p_del_id, existT ftype _  fp_del);
                                               (_q_id, existT ftype _ fq)])
                    in exact z) in
     prove_roundoff_bound (boundsmap_of_list [varinfo_p_del ; varinfo_q])
                          vm
                          update_p_delf_expr (1.7976931348623157 * 10 ^ 308).
  Proof.
    intros; subst.
    prove_roundoff_bound.
    - prove_rndval; interval.
    - prove_roundoff_bound2.
      match goal with |- Rabs ?a <= _ => field_simplify a end.
      interval.
  Qed.
  
  Lemma update_state_var (fK fx fx_del ft fm : ftype Tdouble) :
    let vm := ltac:(let z := compute_PTree (valmap_of_list
                                              [(_K_id, existT ftype _  fK);
                                               (_x_id, existT ftype _ fx);
                                               (_x_del_id, existT ftype _ fx_del);
                                               (_t_id, existT ftype _ ft);
                                               (_m_id, existT ftype _ fm)])
                    in exact z) in
     prove_roundoff_bound (boundsmap_of_list [varinfo_K; varinfo_x; varinfo_x_del; varinfo_t; varinfo_m])
                          vm
                          update_state_expr (1.7976931348623157 * 10 ^ 308).
  Proof.
    intros; subst.
    prove_roundoff_bound.
    - prove_rndval; interval.
    - prove_roundoff_bound2.
      match goal with |- Rabs ?a <= _ => field_simplify a end.
      interval.
  Qed.
  
  Lemma update_p_var (fK fp fp_del ft fq : ftype Tdouble) :
    let vm := ltac:(let z := compute_PTree (valmap_of_list
                                              [(_K_id, existT ftype _  fK);
                                               (_p_id, existT ftype _ fp);
                                               (_p_del_id, existT ftype _ fp_del);
                                               (_t_id, existT ftype _ ft);
                                               (_q_id, existT ftype _ fq)])
                    in exact z) in
     prove_roundoff_bound (boundsmap_of_list [varinfo_K; varinfo_p; varinfo_p_del; varinfo_t; varinfo_q])
                          vm
                          update_p_expr (1.7976931348623157 * 10 ^ 308).
  Proof.
    intros; subst.
    prove_roundoff_bound.
    - prove_rndval; interval.
    - prove_roundoff_bound2.
      match goal with |- Rabs ?a <= _ => field_simplify a end.
      interval.
  Qed.
  
  Lemma update_gain_var (fp fr : ftype Tdouble) :
    let vm := ltac:(let z := compute_PTree (valmap_of_list
                                              [(_p_id, existT ftype _  fp);
                                               (_r_id, existT ftype _ fr)])
                    in exact z) in
     prove_roundoff_bound (boundsmap_of_list [varinfo_p; varinfo_r])
                          vm
                          update_gain_expr (1.7976931348623157 * 10 ^ 308).
  Proof.
    intros; subst.
    prove_roundoff_bound.
    - prove_rndval; interval.
    - prove_roundoff_bound2.
      match goal with |- Rabs ?a <= _ => field_simplify a end; try interval; split; intro; [lra|].
      rewrite Rcomplements.Rabs_le_between in *.
      assert (2 * (1 + e2) <= (FT2R fp + FT2R fr) * (1 + e2)) as P by (apply Rmult_le_compat_r; lra).
      lra.
  Qed.
  
End fidelity.
