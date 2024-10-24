From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.13".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "kettle2.c".
  Definition normalized := false.
End Info.

Definition _K : ident := $"K".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_cls : ident := $"__builtin_cls".
Definition ___builtin_clsl : ident := $"__builtin_clsl".
Definition ___builtin_clsll : ident := $"__builtin_clsll".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fence : ident := $"__builtin_fence".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _i : ident := $"i".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _p : ident := $"p".
Definition _p_del : ident := $"p_del".
Definition _p_del_var : ident := $"p_del_var".
Definition _p_var : ident := $"p_var".
Definition _q : ident := $"q".
Definition _r : ident := $"r".
Definition _r_var : ident := $"r_var".
Definition _rate : ident := $"rate".
Definition _sensor_data : ident := $"sensor_data".
Definition _t : ident := $"t".
Definition _temp : ident := $"temp".
Definition _update_gain : ident := $"update_gain".
Definition _update_p : ident := $"update_p".
Definition _update_p_del : ident := $"update_p_del".
Definition _update_state : ident := $"update_state".
Definition _x : ident := $"x".
Definition _x_del : ident := $"x_del".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.

Definition f_update_p := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_K, tdouble) :: (_p, tdouble) :: (_p_del, tdouble) ::
                (_t, tdouble) :: (_q, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd
                 (Ebinop Oadd
                   (Ebinop Omul
                     (Ebinop Osub
                       (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
                       (Etempvar _K tdouble) tdouble) (Etempvar _p tdouble)
                     tdouble)
                   (Ebinop Omul
                     (Ebinop Omul (Etempvar _t tdouble) (Etempvar _t tdouble)
                       tdouble) (Etempvar _p_del tdouble) tdouble) tdouble)
                 (Etempvar _q tdouble) tdouble)))
|}.

Definition f_update_state := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_K, tdouble) :: (_x, tdouble) :: (_x_del, tdouble) ::
                (_t, tdouble) :: (_m, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd
                 (Ebinop Oadd (Etempvar _x tdouble)
                   (Ebinop Omul (Etempvar _t tdouble)
                     (Etempvar _x_del tdouble) tdouble) tdouble)
                 (Ebinop Omul (Etempvar _K tdouble)
                   (Ebinop Osub (Etempvar _m tdouble) (Etempvar _x tdouble)
                     tdouble) tdouble) tdouble)))
|}.

Definition f_update_p_del := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_p_del, tdouble) :: (_q, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd (Etempvar _p_del tdouble) (Etempvar _q tdouble)
                 tdouble)))
|}.

Definition f_update_gain := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_p, tdouble) :: (_r, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Odiv (Etempvar _p tdouble)
                 (Ebinop Oadd (Etempvar _p tdouble) (Etempvar _r tdouble)
                   tdouble) tdouble)))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_sensor_data, (tarray tdouble 14)) :: nil);
  fn_temps := ((_m, tdouble) :: (_K, tdouble) :: (_t, tdouble) ::
               (_temp, tdouble) :: (_rate, tdouble) :: (_p_var, tdouble) ::
               (_p_del_var, tdouble) :: (_r_var, tdouble) :: (_q, tdouble) ::
               (_i, tint) :: (_t'4, tdouble) :: (_t'3, tdouble) ::
               (_t'2, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _sensor_data (tarray tdouble 14))
          (Econst_int (Int.repr 0) tint) (tptr tdouble)) tdouble)
      (Econst_float (Float.of_bits (Int64.repr 4626238274723328819)) tdouble))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _sensor_data (tarray tdouble 14))
            (Econst_int (Int.repr 1) tint) (tptr tdouble)) tdouble)
        (Econst_float (Float.of_bits (Int64.repr 4626421233458190746)) tdouble))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _sensor_data (tarray tdouble 14))
              (Econst_int (Int.repr 2) tint) (tptr tdouble)) tdouble)
          (Econst_float (Float.of_bits (Int64.repr 4626348049964245975)) tdouble))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _sensor_data (tarray tdouble 14))
                (Econst_int (Int.repr 3) tint) (tptr tdouble)) tdouble)
            (Econst_float (Float.of_bits (Int64.repr 4626615451192121098)) tdouble))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _sensor_data (tarray tdouble 14))
                  (Econst_int (Int.repr 4) tint) (tptr tdouble)) tdouble)
              (Econst_float (Float.of_bits (Int64.repr 4625700657517811466)) tdouble))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _sensor_data (tarray tdouble 14))
                    (Econst_int (Int.repr 5) tint) (tptr tdouble)) tdouble)
                (Econst_float (Float.of_bits (Int64.repr 4626607006942819779)) tdouble))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _sensor_data (tarray tdouble 14))
                      (Econst_int (Int.repr 6) tint) (tptr tdouble)) tdouble)
                  (Econst_float (Float.of_bits (Int64.repr 4626956035913940992)) tdouble))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _sensor_data (tarray tdouble 14))
                        (Econst_int (Int.repr 7) tint) (tptr tdouble))
                      tdouble)
                    (Econst_float (Float.of_bits (Int64.repr 4627141809398570025)) tdouble))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _sensor_data (tarray tdouble 14))
                          (Econst_int (Int.repr 8) tint) (tptr tdouble))
                        tdouble)
                      (Econst_float (Float.of_bits (Int64.repr 4627882088587319050)) tdouble))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Evar _sensor_data (tarray tdouble 14))
                            (Econst_int (Int.repr 9) tint) (tptr tdouble))
                          tdouble)
                        (Econst_float (Float.of_bits (Int64.repr 4629027691742531420)) tdouble))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Evar _sensor_data (tarray tdouble 14))
                              (Econst_int (Int.repr 10) tint) (tptr tdouble))
                            tdouble)
                          (Econst_float (Float.of_bits (Int64.repr 4629244427474598625)) tdouble))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Evar _sensor_data (tarray tdouble 14))
                                (Econst_int (Int.repr 11) tint)
                                (tptr tdouble)) tdouble)
                            (Econst_float (Float.of_bits (Int64.repr 4629216279976927560)) tdouble))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _sensor_data (tarray tdouble 14))
                                  (Econst_int (Int.repr 12) tint)
                                  (tptr tdouble)) tdouble)
                              (Econst_float (Float.of_bits (Int64.repr 4629943892791724605)) tdouble))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _sensor_data (tarray tdouble 14))
                                    (Econst_int (Int.repr 13) tint)
                                    (tptr tdouble)) tdouble)
                                (Econst_float (Float.of_bits (Int64.repr 4630222553018668155)) tdouble))
                              (Ssequence
                                (Sset _t
                                  (Econst_float (Float.of_bits (Int64.repr 4617315517961601024)) tdouble))
                                (Ssequence
                                  (Sset _temp
                                    (Econst_float (Float.of_bits (Int64.repr 4625196817309499392)) tdouble))
                                  (Ssequence
                                    (Sset _rate
                                      (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                                    (Ssequence
                                      (Sset _p_var
                                        (Econst_float (Float.of_bits (Int64.repr 4636737291354636288)) tdouble))
                                      (Ssequence
                                        (Sset _p_del_var
                                          (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                                        (Ssequence
                                          (Sset _r_var
                                            (Econst_float (Float.of_bits (Int64.repr 4625196817309499392)) tdouble))
                                          (Ssequence
                                            (Sset _q
                                              (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _i
                                                  (Econst_int (Int.repr 0) tint))
                                                (Sloop
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Olt
                                                                   (Etempvar _i tint)
                                                                   (Econst_int (Int.repr 14) tint)
                                                                   tint)
                                                      Sskip
                                                      Sbreak)
                                                    (Ssequence
                                                      (Sset _m
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _sensor_data (tarray tdouble 14))
                                                            (Etempvar _i tint)
                                                            (tptr tdouble))
                                                          tdouble))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'1)
                                                            (Evar _update_gain 
                                                            (Tfunction
                                                              (Tcons tdouble
                                                                (Tcons
                                                                  tdouble
                                                                  Tnil))
                                                              tdouble
                                                              cc_default))
                                                            ((Etempvar _p_var tdouble) ::
                                                             (Etempvar _r_var tdouble) ::
                                                             nil))
                                                          (Sset _K
                                                            (Etempvar _t'1 tdouble)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Scall (Some _t'2)
                                                              (Evar _update_state 
                                                              (Tfunction
                                                                (Tcons
                                                                  tdouble
                                                                  (Tcons
                                                                    tdouble
                                                                    (Tcons
                                                                    tdouble
                                                                    (Tcons
                                                                    tdouble
                                                                    (Tcons
                                                                    tdouble
                                                                    Tnil)))))
                                                                tdouble
                                                                cc_default))
                                                              ((Etempvar _K tdouble) ::
                                                               (Etempvar _m tdouble) ::
                                                               (Etempvar _rate tdouble) ::
                                                               (Etempvar _t tdouble) ::
                                                               (Etempvar _m tdouble) ::
                                                               nil))
                                                            (Sset _temp
                                                              (Etempvar _t'2 tdouble)))
                                                          (Ssequence
                                                            (Sset _rate
                                                              (Etempvar _rate tdouble))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Scall (Some _t'3)
                                                                  (Evar _update_p 
                                                                  (Tfunction
                                                                    (Tcons
                                                                    tdouble
                                                                    (Tcons
                                                                    tdouble
                                                                    (Tcons
                                                                    tdouble
                                                                    (Tcons
                                                                    tdouble
                                                                    (Tcons
                                                                    tdouble
                                                                    Tnil)))))
                                                                    tdouble
                                                                    cc_default))
                                                                  ((Etempvar _K tdouble) ::
                                                                   (Etempvar _p_var tdouble) ::
                                                                   (Etempvar _p_del_var tdouble) ::
                                                                   (Etempvar _t tdouble) ::
                                                                   (Etempvar _q tdouble) ::
                                                                   nil))
                                                                (Sset _p_var
                                                                  (Etempvar _t'3 tdouble)))
                                                              (Ssequence
                                                                (Scall (Some _t'4)
                                                                  (Evar _update_p_del 
                                                                  (Tfunction
                                                                    (Tcons
                                                                    tdouble
                                                                    (Tcons
                                                                    tdouble
                                                                    Tnil))
                                                                    tdouble
                                                                    cc_default))
                                                                  ((Etempvar _p_del_var tdouble) ::
                                                                   (Econst_float (Float.of_bits (Int64.repr 0)) tdouble) ::
                                                                   nil))
                                                                (Sset _p_del_var
                                                                  (Etempvar _t'4 tdouble)))))))))
                                                  (Sset _i
                                                    (Ebinop Oadd
                                                      (Etempvar _i tint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tint))))
                                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_fence,
   Gfun(External (EF_builtin "__builtin_fence"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_update_p, Gfun(Internal f_update_p)) ::
 (_update_state, Gfun(Internal f_update_state)) ::
 (_update_p_del, Gfun(Internal f_update_p_del)) ::
 (_update_gain, Gfun(Internal f_update_gain)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _update_gain :: _update_p_del :: _update_state :: _update_p ::
 ___builtin_debug :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
 ___builtin_fence :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


