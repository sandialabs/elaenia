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
  Definition source_file := "Matrix_Algebra.c".
  Definition normalized := true.
End Info.

Definition _C : ident := $"C".
Definition _Matrix_Error : ident := $"Matrix_Error".
Definition __1543 : ident := $"_1543".
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
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition _a : ident := $"a".
Definition _a_copy : ident := $"a_copy".
Definition _ai : ident := $"ai".
Definition _ai_copy : ident := $"ai_copy".
Definition _ainv : ident := $"ainv".
Definition _ap : ident := $"ap".
Definition _axb : ident := $"axb".
Definition _b : ident := $"b".
Definition _big : ident := $"big".
Definition _c : ident := $"c".
Definition _col : ident := $"col".
Definition _d : ident := $"d".
Definition _dum : ident := $"dum".
Definition _fabs : ident := $"fabs".
Definition _i : ident := $"i".
Definition _ii : ident := $"ii".
Definition _imax : ident := $"imax".
Definition _indx : ident := $"indx".
Definition _ip : ident := $"ip".
Definition _j : ident := $"j".
Definition _j__1 : ident := $"j__1".
Definition _k : ident := $"k".
Definition _k__1 : ident := $"k__1".
Definition _lu_bksb : ident := $"lu_bksb".
Definition _lu_dcmp : ident := $"lu_dcmp".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _msg : ident := $"msg".
Definition _n : ident := $"n".
Definition _printf : ident := $"printf".
Definition _r : ident := $"r".
Definition _ret : ident := $"ret".
Definition _sum : ident := $"sum".
Definition _temp : ident := $"temp".
Definition _vv : ident := $"vv".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 3);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 38);
  gvar_init := (Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 34);
  gvar_init := (Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_Matrix_Error := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_msg, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
  ((Evar ___stringlit_1 (tarray tschar 3)) ::
   (Etempvar _msg (tptr tschar)) :: nil))
|}.

Definition f_axb := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr (Tstruct __1543 noattr))) ::
                (_b, (tptr (Tstruct __1543 noattr))) ::
                (_C, (tptr (Tstruct __1543 noattr))) :: nil);
  fn_vars := ((_ret, (Tstruct __1543 noattr)) :: nil);
  fn_temps := ((_r, tint) :: (_c, tint) :: (_i, tint) :: (_j, tint) ::
               (_k, tint) :: (_j__1, tint) :: (_k__1, tint) ::
               (_t'13, tint) :: (_t'12, tint) :: (_t'11, tint) ::
               (_t'10, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tdouble) :: (_t'5, tdouble) ::
               (_t'4, tdouble) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _j (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                       (Econst_int (Int.repr 20) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _k (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _k tint)
                             (Econst_int (Int.repr 20) tint) tint)
                Sskip
                Sbreak)
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Ederef
                      (Ebinop Oadd
                        (Efield (Evar _ret (Tstruct __1543 noattr)) _a
                          (tarray (tarray tdouble 20) 20)) (Etempvar _j tint)
                        (tptr (tarray tdouble 20))) (tarray tdouble 20))
                    (Etempvar _k tint) (tptr tdouble)) tdouble)
                (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)))
            (Sset _k
              (Ebinop Oadd (Etempvar _k tint) (Econst_int (Int.repr 1) tint)
                tint)))))
      (Sset _j
        (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Sset _t'13
        (Efield
          (Ederef (Etempvar _a (tptr (Tstruct __1543 noattr)))
            (Tstruct __1543 noattr)) _m tint))
      (Sassign (Efield (Evar _ret (Tstruct __1543 noattr)) _m tint)
        (Etempvar _t'13 tint)))
    (Ssequence
      (Ssequence
        (Sset _t'12
          (Efield
            (Ederef (Etempvar _b (tptr (Tstruct __1543 noattr)))
              (Tstruct __1543 noattr)) _n tint))
        (Sassign (Efield (Evar _ret (Tstruct __1543 noattr)) _n tint)
          (Etempvar _t'12 tint)))
      (Ssequence
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _a (tptr (Tstruct __1543 noattr)))
                (Tstruct __1543 noattr)) _n tint))
          (Ssequence
            (Sset _t'11
              (Efield
                (Ederef (Etempvar _b (tptr (Tstruct __1543 noattr)))
                  (Tstruct __1543 noattr)) _m tint))
            (Sifthenelse (Ebinop One (Etempvar _t'10 tint)
                           (Etempvar _t'11 tint) tint)
              (Scall None
                (Evar _Matrix_Error (Tfunction (Tcons (tptr tschar) Tnil)
                                      tvoid cc_default))
                ((Evar ___stringlit_2 (tarray tschar 34)) :: nil))
              Sskip)))
        (Ssequence
          (Ssequence
            (Sset _r (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef (Etempvar _a (tptr (Tstruct __1543 noattr)))
                        (Tstruct __1543 noattr)) _m tint))
                  (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                                 (Etempvar _t'9 tint) tint)
                    Sskip
                    Sbreak))
                (Ssequence
                  (Sset _c (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Ssequence
                        (Sset _t'8
                          (Efield
                            (Ederef
                              (Etempvar _b (tptr (Tstruct __1543 noattr)))
                              (Tstruct __1543 noattr)) _n tint))
                        (Sifthenelse (Ebinop Olt (Etempvar _c tint)
                                       (Etempvar _t'8 tint) tint)
                          Sskip
                          Sbreak))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Ederef
                                (Ebinop Oadd
                                  (Efield (Evar _ret (Tstruct __1543 noattr))
                                    _a (tarray (tarray tdouble 20) 20))
                                  (Etempvar _r tint)
                                  (tptr (tarray tdouble 20)))
                                (tarray tdouble 20)) (Etempvar _c tint)
                              (tptr tdouble)) tdouble)
                          (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                        (Ssequence
                          (Sset _i (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Ssequence
                                (Sset _t'7
                                  (Efield
                                    (Ederef
                                      (Etempvar _a (tptr (Tstruct __1543 noattr)))
                                      (Tstruct __1543 noattr)) _n tint))
                                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                               (Etempvar _t'7 tint) tint)
                                  Sskip
                                  Sbreak))
                              (Ssequence
                                (Sset _t'4
                                  (Ederef
                                    (Ebinop Oadd
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Evar _ret (Tstruct __1543 noattr))
                                            _a
                                            (tarray (tarray tdouble 20) 20))
                                          (Etempvar _r tint)
                                          (tptr (tarray tdouble 20)))
                                        (tarray tdouble 20))
                                      (Etempvar _c tint) (tptr tdouble))
                                    tdouble))
                                (Ssequence
                                  (Sset _t'5
                                    (Ederef
                                      (Ebinop Oadd
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _a (tptr (Tstruct __1543 noattr)))
                                                (Tstruct __1543 noattr)) _a
                                              (tarray (tarray tdouble 20) 20))
                                            (Etempvar _r tint)
                                            (tptr (tarray tdouble 20)))
                                          (tarray tdouble 20))
                                        (Etempvar _i tint) (tptr tdouble))
                                      tdouble))
                                  (Ssequence
                                    (Sset _t'6
                                      (Ederef
                                        (Ebinop Oadd
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _b (tptr (Tstruct __1543 noattr)))
                                                  (Tstruct __1543 noattr)) _a
                                                (tarray (tarray tdouble 20) 20))
                                              (Etempvar _i tint)
                                              (tptr (tarray tdouble 20)))
                                            (tarray tdouble 20))
                                          (Etempvar _c tint) (tptr tdouble))
                                        tdouble))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Evar _ret (Tstruct __1543 noattr))
                                                _a
                                                (tarray (tarray tdouble 20) 20))
                                              (Etempvar _r tint)
                                              (tptr (tarray tdouble 20)))
                                            (tarray tdouble 20))
                                          (Etempvar _c tint) (tptr tdouble))
                                        tdouble)
                                      (Ebinop Oadd (Etempvar _t'4 tdouble)
                                        (Ebinop Omul (Etempvar _t'5 tdouble)
                                          (Etempvar _t'6 tdouble) tdouble)
                                        tdouble))))))
                            (Sset _i
                              (Ebinop Oadd (Etempvar _i tint)
                                (Econst_int (Int.repr 1) tint) tint))))))
                    (Sset _c
                      (Ebinop Oadd (Etempvar _c tint)
                        (Econst_int (Int.repr 1) tint) tint)))))
              (Sset _r
                (Ebinop Oadd (Etempvar _r tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield (Evar _ret (Tstruct __1543 noattr)) _m tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _C (tptr (Tstruct __1543 noattr)))
                    (Tstruct __1543 noattr)) _m tint) (Etempvar _t'3 tint)))
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Efield (Evar _ret (Tstruct __1543 noattr)) _n tint))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _C (tptr (Tstruct __1543 noattr)))
                      (Tstruct __1543 noattr)) _n tint) (Etempvar _t'2 tint)))
              (Ssequence
                (Sset _j__1 (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _j__1 tint)
                                   (Econst_int (Int.repr 20) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _k__1 (Econst_int (Int.repr 0) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _k__1 tint)
                                         (Econst_int (Int.repr 20) tint)
                                         tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Sset _t'1
                              (Ederef
                                (Ebinop Oadd
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Evar _ret (Tstruct __1543 noattr))
                                        _a (tarray (tarray tdouble 20) 20))
                                      (Etempvar _j__1 tint)
                                      (tptr (tarray tdouble 20)))
                                    (tarray tdouble 20))
                                  (Etempvar _k__1 tint) (tptr tdouble))
                                tdouble))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _C (tptr (Tstruct __1543 noattr)))
                                          (Tstruct __1543 noattr)) _a
                                        (tarray (tarray tdouble 20) 20))
                                      (Etempvar _j__1 tint)
                                      (tptr (tarray tdouble 20)))
                                    (tarray tdouble 20))
                                  (Etempvar _k__1 tint) (tptr tdouble))
                                tdouble) (Etempvar _t'1 tdouble))))
                        (Sset _k__1
                          (Ebinop Oadd (Etempvar _k__1 tint)
                            (Econst_int (Int.repr 1) tint) tint)))))
                  (Sset _j__1
                    (Ebinop Oadd (Etempvar _j__1 tint)
                      (Econst_int (Int.repr 1) tint) tint)))))))))))
|}.

Definition f_lu_bksb := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tdouble)) :: (_n, tint) :: (_indx, (tptr tint)) ::
                (_b, (tptr tdouble)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_ii, tint) :: (_ip, tint) :: (_j, tint) ::
               (_sum, tdouble) :: (_t'6, tdouble) :: (_t'5, tdouble) ::
               (_t'4, tdouble) :: (_t'3, tdouble) :: (_t'2, tdouble) ::
               (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sset _ii (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _n tint)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _ip
              (Ederef
                (Ebinop Oadd (Etempvar _indx (tptr tint)) (Etempvar _i tint)
                  (tptr tint)) tint))
            (Ssequence
              (Sset _sum
                (Ederef
                  (Ebinop Oadd (Etempvar _b (tptr tdouble))
                    (Etempvar _ip tint) (tptr tdouble)) tdouble))
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Ederef
                      (Ebinop Oadd (Etempvar _b (tptr tdouble))
                        (Etempvar _i tint) (tptr tdouble)) tdouble))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _b (tptr tdouble))
                        (Etempvar _ip tint) (tptr tdouble)) tdouble)
                    (Etempvar _t'6 tdouble)))
                (Ssequence
                  (Sifthenelse (Ebinop One (Etempvar _ii tint)
                                 (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                   tint) tint)
                    (Ssequence
                      (Sset _j (Etempvar _ii tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Ole (Etempvar _j tint)
                                         (Ebinop Osub (Etempvar _i tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint) tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Sset _t'4
                              (Ederef
                                (Ebinop Oadd (Etempvar _a (tptr tdouble))
                                  (Ebinop Oadd
                                    (Ebinop Omul (Etempvar _i tint)
                                      (Etempvar _n tint) tint)
                                    (Etempvar _j tint) tint) (tptr tdouble))
                                tdouble))
                            (Ssequence
                              (Sset _t'5
                                (Ederef
                                  (Ebinop Oadd (Etempvar _b (tptr tdouble))
                                    (Etempvar _j tint) (tptr tdouble))
                                  tdouble))
                              (Sset _sum
                                (Ebinop Osub (Etempvar _sum tdouble)
                                  (Ebinop Omul (Etempvar _t'4 tdouble)
                                    (Etempvar _t'5 tdouble) tdouble) tdouble)))))
                        (Sset _j
                          (Ebinop Oadd (Etempvar _j tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    (Sifthenelse (Etempvar _sum tdouble)
                      (Sset _ii (Etempvar _i tint))
                      Sskip))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _b (tptr tdouble))
                        (Etempvar _i tint) (tptr tdouble)) tdouble)
                    (Etempvar _sum tdouble)))))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sset _i
        (Ebinop Osub (Etempvar _n tint) (Econst_int (Int.repr 1) tint) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                         (Econst_int (Int.repr 0) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _sum
              (Ederef
                (Ebinop Oadd (Etempvar _b (tptr tdouble)) (Etempvar _i tint)
                  (tptr tdouble)) tdouble))
            (Ssequence
              (Ssequence
                (Sset _j
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                   (Etempvar _n tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _t'2
                        (Ederef
                          (Ebinop Oadd (Etempvar _a (tptr tdouble))
                            (Ebinop Oadd
                              (Ebinop Omul (Etempvar _i tint)
                                (Etempvar _n tint) tint) (Etempvar _j tint)
                              tint) (tptr tdouble)) tdouble))
                      (Ssequence
                        (Sset _t'3
                          (Ederef
                            (Ebinop Oadd (Etempvar _b (tptr tdouble))
                              (Etempvar _j tint) (tptr tdouble)) tdouble))
                        (Sset _sum
                          (Ebinop Osub (Etempvar _sum tdouble)
                            (Ebinop Omul (Etempvar _t'2 tdouble)
                              (Etempvar _t'3 tdouble) tdouble) tdouble)))))
                  (Sset _j
                    (Ebinop Oadd (Etempvar _j tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd (Etempvar _a (tptr tdouble))
                      (Ebinop Oadd
                        (Ebinop Omul (Etempvar _i tint) (Etempvar _n tint)
                          tint) (Etempvar _i tint) tint) (tptr tdouble))
                    tdouble))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _b (tptr tdouble))
                      (Etempvar _i tint) (tptr tdouble)) tdouble)
                  (Ebinop Odiv (Etempvar _sum tdouble)
                    (Etempvar _t'1 tdouble) tdouble))))))
        (Sset _i
          (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))))
|}.

Definition f_ainv := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr (Tstruct __1543 noattr))) ::
                (_ai, (tptr (Tstruct __1543 noattr))) :: nil);
  fn_vars := ((_a_copy, (tarray tdouble 400)) ::
              (_ai_copy, (tarray tdouble 400)) ::
              (_indx, (tarray tint 20)) :: (_col, (tarray tdouble 20)) ::
              (_d, tfloat) :: nil);
  fn_temps := ((_i, tint) :: (_j, tint) :: (_t'15, tint) :: (_t'14, tint) ::
               (_t'13, tdouble) :: (_t'12, tint) :: (_t'11, tint) ::
               (_t'10, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tdouble) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tdouble) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _t'15
            (Efield
              (Ederef (Etempvar _a (tptr (Tstruct __1543 noattr)))
                (Tstruct __1543 noattr)) _m tint))
          (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _t'15 tint)
                         tint)
            Sskip
            Sbreak))
        (Ssequence
          (Sset _j (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Ssequence
                (Sset _t'14
                  (Efield
                    (Ederef (Etempvar _a (tptr (Tstruct __1543 noattr)))
                      (Tstruct __1543 noattr)) _n tint))
                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                               (Etempvar _t'14 tint) tint)
                  Sskip
                  Sbreak))
              (Ssequence
                (Sset _t'12
                  (Efield
                    (Ederef (Etempvar _a (tptr (Tstruct __1543 noattr)))
                      (Tstruct __1543 noattr)) _n tint))
                (Ssequence
                  (Sset _t'13
                    (Ederef
                      (Ebinop Oadd
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _a (tptr (Tstruct __1543 noattr)))
                                (Tstruct __1543 noattr)) _a
                              (tarray (tarray tdouble 20) 20))
                            (Etempvar _i tint) (tptr (tarray tdouble 20)))
                          (tarray tdouble 20)) (Etempvar _j tint)
                        (tptr tdouble)) tdouble))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _a_copy (tarray tdouble 400))
                        (Ebinop Oadd
                          (Ebinop Omul (Etempvar _i tint)
                            (Etempvar _t'12 tint) tint) (Etempvar _j tint)
                          tint) (tptr tdouble)) tdouble)
                    (Etempvar _t'13 tdouble)))))
            (Sset _j
              (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
                tint)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Sset _t'11
        (Efield
          (Ederef (Etempvar _a (tptr (Tstruct __1543 noattr)))
            (Tstruct __1543 noattr)) _n tint))
      (Scall None
        (Evar _lu_dcmp (Tfunction
                         (Tcons (tptr tdouble)
                           (Tcons tint
                             (Tcons (tptr tint) (Tcons (tptr tfloat) Tnil))))
                         tvoid cc_default))
        ((Evar _a_copy (tarray tdouble 400)) :: (Etempvar _t'11 tint) ::
         (Evar _indx (tarray tint 20)) ::
         (Eaddrof (Evar _d tfloat) (tptr tfloat)) :: nil)))
    (Ssequence
      (Ssequence
        (Sset _j (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef (Etempvar _a (tptr (Tstruct __1543 noattr)))
                    (Tstruct __1543 noattr)) _n tint))
              (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                             (Etempvar _t'10 tint) tint)
                Sskip
                Sbreak))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Sset _t'9
                        (Efield
                          (Ederef
                            (Etempvar _a (tptr (Tstruct __1543 noattr)))
                            (Tstruct __1543 noattr)) _n tint))
                      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                     (Etempvar _t'9 tint) tint)
                        Sskip
                        Sbreak))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _col (tarray tdouble 20))
                          (Etempvar _i tint) (tptr tdouble)) tdouble)
                      (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _col (tarray tdouble 20))
                      (Etempvar _j tint) (tptr tdouble)) tdouble)
                  (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble))
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef (Etempvar _a (tptr (Tstruct __1543 noattr)))
                          (Tstruct __1543 noattr)) _n tint))
                    (Scall None
                      (Evar _lu_bksb (Tfunction
                                       (Tcons (tptr tdouble)
                                         (Tcons tint
                                           (Tcons (tptr tint)
                                             (Tcons (tptr tdouble) Tnil))))
                                       tvoid cc_default))
                      ((Evar _a_copy (tarray tdouble 400)) ::
                       (Etempvar _t'8 tint) ::
                       (Evar _indx (tarray tint 20)) ::
                       (Evar _col (tarray tdouble 20)) :: nil)))
                  (Ssequence
                    (Sset _i (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Ssequence
                          (Sset _t'7
                            (Efield
                              (Ederef
                                (Etempvar _a (tptr (Tstruct __1543 noattr)))
                                (Tstruct __1543 noattr)) _n tint))
                          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                         (Etempvar _t'7 tint) tint)
                            Sskip
                            Sbreak))
                        (Ssequence
                          (Sset _t'5
                            (Efield
                              (Ederef
                                (Etempvar _a (tptr (Tstruct __1543 noattr)))
                                (Tstruct __1543 noattr)) _n tint))
                          (Ssequence
                            (Sset _t'6
                              (Ederef
                                (Ebinop Oadd (Evar _col (tarray tdouble 20))
                                  (Etempvar _i tint) (tptr tdouble)) tdouble))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _ai_copy (tarray tdouble 400))
                                  (Ebinop Oadd
                                    (Ebinop Omul (Etempvar _i tint)
                                      (Etempvar _t'5 tint) tint)
                                    (Etempvar _j tint) tint) (tptr tdouble))
                                tdouble) (Etempvar _t'6 tdouble)))))
                      (Sset _i
                        (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 1) tint) tint))))))))
          (Sset _j
            (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _a (tptr (Tstruct __1543 noattr)))
                    (Tstruct __1543 noattr)) _m tint))
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Etempvar _t'4 tint) tint)
                Sskip
                Sbreak))
            (Ssequence
              (Sset _j (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Ssequence
                    (Sset _t'3
                      (Efield
                        (Ederef (Etempvar _a (tptr (Tstruct __1543 noattr)))
                          (Tstruct __1543 noattr)) _n tint))
                    (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                   (Etempvar _t'3 tint) tint)
                      Sskip
                      Sbreak))
                  (Ssequence
                    (Sset _t'1
                      (Efield
                        (Ederef (Etempvar _a (tptr (Tstruct __1543 noattr)))
                          (Tstruct __1543 noattr)) _n tint))
                    (Ssequence
                      (Sset _t'2
                        (Ederef
                          (Ebinop Oadd (Evar _ai_copy (tarray tdouble 400))
                            (Ebinop Oadd
                              (Ebinop Omul (Etempvar _i tint)
                                (Etempvar _t'1 tint) tint) (Etempvar _j tint)
                              tint) (tptr tdouble)) tdouble))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _a (tptr (Tstruct __1543 noattr)))
                                    (Tstruct __1543 noattr)) _a
                                  (tarray (tarray tdouble 20) 20))
                                (Etempvar _i tint)
                                (tptr (tarray tdouble 20)))
                              (tarray tdouble 20)) (Etempvar _j tint)
                            (tptr tdouble)) tdouble) (Etempvar _t'2 tdouble)))))
                (Sset _j
                  (Ebinop Oadd (Etempvar _j tint)
                    (Econst_int (Int.repr 1) tint) tint)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint)))))))
|}.

Definition f_lu_dcmp := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tdouble)) :: (_n, tint) :: (_indx, (tptr tint)) ::
                (_d, (tptr tfloat)) :: nil);
  fn_vars := ((_vv, (tarray tdouble 20)) :: nil);
  fn_temps := ((_i, tint) :: (_imax, tint) :: (_j, tint) :: (_k, tint) ::
               (_big, tdouble) :: (_dum, tdouble) :: (_sum, tdouble) ::
               (_temp, tdouble) :: (_t'4, tdouble) :: (_t'3, tdouble) ::
               (_t'2, tdouble) :: (_t'1, tdouble) :: (_t'16, tdouble) ::
               (_t'15, tdouble) :: (_t'14, tdouble) :: (_t'13, tdouble) ::
               (_t'12, tdouble) :: (_t'11, tdouble) :: (_t'10, tdouble) ::
               (_t'9, tfloat) :: (_t'8, tdouble) :: (_t'7, tdouble) ::
               (_t'6, tdouble) :: (_t'5, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Ederef (Etempvar _d (tptr tfloat)) tfloat)
    (Ecast
      (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
      tfloat))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _n tint)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _big (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
            (Ssequence
              (Ssequence
                (Sset _j (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                   (Etempvar _n tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'16
                              (Ederef
                                (Ebinop Oadd (Etempvar _a (tptr tdouble))
                                  (Ebinop Oadd
                                    (Ebinop Omul (Etempvar _i tint)
                                      (Etempvar _n tint) tint)
                                    (Etempvar _j tint) tint) (tptr tdouble))
                                tdouble))
                            (Scall (Some _t'1)
                              (Evar _fabs (Tfunction (Tcons tdouble Tnil)
                                            tdouble cc_default))
                              ((Etempvar _t'16 tdouble) :: nil)))
                          (Sset _t'2 (Ecast (Etempvar _t'1 tdouble) tdouble)))
                        (Sset _temp (Etempvar _t'2 tdouble)))
                      (Sifthenelse (Ebinop Ogt (Etempvar _t'2 tdouble)
                                     (Etempvar _big tdouble) tint)
                        (Sset _big (Etempvar _temp tdouble))
                        Sskip)))
                  (Sset _j
                    (Ebinop Oadd (Etempvar _j tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _big tdouble)
                               (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                               tint)
                  (Ssequence
                    (Sset _big
                      (Eunop Oneg
                        (Econst_float (Float.of_bits (Int64.repr 6088095589093318446)) tdouble)
                        tdouble))
                    (Ssequence
                      (Scall None
                        (Evar _Matrix_Error (Tfunction
                                              (Tcons (tptr tschar) Tnil)
                                              tvoid cc_default))
                        ((Evar ___stringlit_3 (tarray tschar 38)) :: nil))
                      (Swhile
                        (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                        Sskip)))
                  Sskip)
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _vv (tarray tdouble 20))
                      (Etempvar _i tint) (tptr tdouble)) tdouble)
                  (Ebinop Odiv
                    (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
                    (Etempvar _big tdouble) tdouble))))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sset _j (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _j tint) (Etempvar _n tint)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Etempvar _j tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _sum
                      (Ederef
                        (Ebinop Oadd (Etempvar _a (tptr tdouble))
                          (Ebinop Oadd
                            (Ebinop Omul (Etempvar _i tint)
                              (Etempvar _n tint) tint) (Etempvar _j tint)
                            tint) (tptr tdouble)) tdouble))
                    (Ssequence
                      (Ssequence
                        (Sset _k (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _k tint)
                                           (Etempvar _i tint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _t'14
                                (Ederef
                                  (Ebinop Oadd (Etempvar _a (tptr tdouble))
                                    (Ebinop Oadd
                                      (Ebinop Omul (Etempvar _i tint)
                                        (Etempvar _n tint) tint)
                                      (Etempvar _k tint) tint)
                                    (tptr tdouble)) tdouble))
                              (Ssequence
                                (Sset _t'15
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _a (tptr tdouble))
                                      (Ebinop Oadd
                                        (Ebinop Omul (Etempvar _k tint)
                                          (Etempvar _n tint) tint)
                                        (Etempvar _j tint) tint)
                                      (tptr tdouble)) tdouble))
                                (Sset _sum
                                  (Ebinop Osub (Etempvar _sum tdouble)
                                    (Ebinop Omul (Etempvar _t'14 tdouble)
                                      (Etempvar _t'15 tdouble) tdouble)
                                    tdouble)))))
                          (Sset _k
                            (Ebinop Oadd (Etempvar _k tint)
                              (Econst_int (Int.repr 1) tint) tint))))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _a (tptr tdouble))
                            (Ebinop Oadd
                              (Ebinop Omul (Etempvar _i tint)
                                (Etempvar _n tint) tint) (Etempvar _j tint)
                              tint) (tptr tdouble)) tdouble)
                        (Etempvar _sum tdouble)))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sset _imax (Etempvar _j tint))
              (Ssequence
                (Sset _big
                  (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                (Ssequence
                  (Ssequence
                    (Sset _i (Etempvar _j tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                       (Etempvar _n tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Sset _sum
                            (Ederef
                              (Ebinop Oadd (Etempvar _a (tptr tdouble))
                                (Ebinop Oadd
                                  (Ebinop Omul (Etempvar _i tint)
                                    (Etempvar _n tint) tint)
                                  (Etempvar _j tint) tint) (tptr tdouble))
                              tdouble))
                          (Ssequence
                            (Ssequence
                              (Sset _k (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt (Etempvar _k tint)
                                                 (Etempvar _j tint) tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _t'12
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _a (tptr tdouble))
                                          (Ebinop Oadd
                                            (Ebinop Omul (Etempvar _i tint)
                                              (Etempvar _n tint) tint)
                                            (Etempvar _k tint) tint)
                                          (tptr tdouble)) tdouble))
                                    (Ssequence
                                      (Sset _t'13
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _a (tptr tdouble))
                                            (Ebinop Oadd
                                              (Ebinop Omul (Etempvar _k tint)
                                                (Etempvar _n tint) tint)
                                              (Etempvar _j tint) tint)
                                            (tptr tdouble)) tdouble))
                                      (Sset _sum
                                        (Ebinop Osub (Etempvar _sum tdouble)
                                          (Ebinop Omul
                                            (Etempvar _t'12 tdouble)
                                            (Etempvar _t'13 tdouble) tdouble)
                                          tdouble)))))
                                (Sset _k
                                  (Ebinop Oadd (Etempvar _k tint)
                                    (Econst_int (Int.repr 1) tint) tint))))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Etempvar _a (tptr tdouble))
                                    (Ebinop Oadd
                                      (Ebinop Omul (Etempvar _i tint)
                                        (Etempvar _n tint) tint)
                                      (Etempvar _j tint) tint)
                                    (tptr tdouble)) tdouble)
                                (Etempvar _sum tdouble))
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'3)
                                      (Evar _fabs (Tfunction
                                                    (Tcons tdouble Tnil)
                                                    tdouble cc_default))
                                      ((Etempvar _sum tdouble) :: nil))
                                    (Ssequence
                                      (Sset _t'11
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _vv (tarray tdouble 20))
                                            (Etempvar _i tint)
                                            (tptr tdouble)) tdouble))
                                      (Sset _t'4
                                        (Ecast
                                          (Ebinop Omul
                                            (Etempvar _t'11 tdouble)
                                            (Etempvar _t'3 tdouble) tdouble)
                                          tdouble))))
                                  (Sset _dum (Etempvar _t'4 tdouble)))
                                (Sifthenelse (Ebinop Oge
                                               (Etempvar _t'4 tdouble)
                                               (Etempvar _big tdouble) tint)
                                  (Ssequence
                                    (Sset _big (Etempvar _dum tdouble))
                                    (Sset _imax (Etempvar _i tint)))
                                  Sskip))))))
                      (Sset _i
                        (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 1) tint) tint))))
                  (Ssequence
                    (Sifthenelse (Ebinop One (Etempvar _j tint)
                                   (Etempvar _imax tint) tint)
                      (Ssequence
                        (Ssequence
                          (Sset _k (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _k tint)
                                             (Etempvar _n tint) tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Sset _dum
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _a (tptr tdouble))
                                      (Ebinop Oadd
                                        (Ebinop Omul (Etempvar _imax tint)
                                          (Etempvar _n tint) tint)
                                        (Etempvar _k tint) tint)
                                      (tptr tdouble)) tdouble))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'10
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _a (tptr tdouble))
                                          (Ebinop Oadd
                                            (Ebinop Omul (Etempvar _j tint)
                                              (Etempvar _n tint) tint)
                                            (Etempvar _k tint) tint)
                                          (tptr tdouble)) tdouble))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _a (tptr tdouble))
                                          (Ebinop Oadd
                                            (Ebinop Omul
                                              (Etempvar _imax tint)
                                              (Etempvar _n tint) tint)
                                            (Etempvar _k tint) tint)
                                          (tptr tdouble)) tdouble)
                                      (Etempvar _t'10 tdouble)))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _a (tptr tdouble))
                                        (Ebinop Oadd
                                          (Ebinop Omul (Etempvar _j tint)
                                            (Etempvar _n tint) tint)
                                          (Etempvar _k tint) tint)
                                        (tptr tdouble)) tdouble)
                                    (Etempvar _dum tdouble)))))
                            (Sset _k
                              (Ebinop Oadd (Etempvar _k tint)
                                (Econst_int (Int.repr 1) tint) tint))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'9
                              (Ederef (Etempvar _d (tptr tfloat)) tfloat))
                            (Sassign
                              (Ederef (Etempvar _d (tptr tfloat)) tfloat)
                              (Eunop Oneg (Etempvar _t'9 tfloat) tfloat)))
                          (Ssequence
                            (Sset _t'8
                              (Ederef
                                (Ebinop Oadd (Evar _vv (tarray tdouble 20))
                                  (Etempvar _j tint) (tptr tdouble)) tdouble))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _vv (tarray tdouble 20))
                                  (Etempvar _imax tint) (tptr tdouble))
                                tdouble) (Etempvar _t'8 tdouble)))))
                      Sskip)
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _indx (tptr tint))
                            (Etempvar _j tint) (tptr tint)) tint)
                        (Etempvar _imax tint))
                      (Ssequence
                        (Ssequence
                          (Sset _t'7
                            (Ederef
                              (Ebinop Oadd (Etempvar _a (tptr tdouble))
                                (Ebinop Oadd
                                  (Ebinop Omul (Etempvar _j tint)
                                    (Etempvar _n tint) tint)
                                  (Etempvar _j tint) tint) (tptr tdouble))
                              tdouble))
                          (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tdouble)
                                         (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                                         tint)
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _a (tptr tdouble))
                                  (Ebinop Oadd
                                    (Ebinop Omul (Etempvar _j tint)
                                      (Etempvar _n tint) tint)
                                    (Etempvar _j tint) tint) (tptr tdouble))
                                tdouble)
                              (Eunop Oneg
                                (Econst_float (Float.of_bits (Int64.repr 6088095589093318446)) tdouble)
                                tdouble))
                            Sskip))
                        (Sifthenelse (Ebinop One (Etempvar _j tint)
                                       (Ebinop Osub (Etempvar _n tint)
                                         (Econst_int (Int.repr 1) tint) tint)
                                       tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'6
                                (Ederef
                                  (Ebinop Oadd (Etempvar _a (tptr tdouble))
                                    (Ebinop Oadd
                                      (Ebinop Omul (Etempvar _j tint)
                                        (Etempvar _n tint) tint)
                                      (Etempvar _j tint) tint)
                                    (tptr tdouble)) tdouble))
                              (Sset _dum
                                (Ebinop Odiv
                                  (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
                                  (Etempvar _t'6 tdouble) tdouble)))
                            (Ssequence
                              (Sset _i
                                (Ebinop Oadd (Etempvar _j tint)
                                  (Econst_int (Int.repr 1) tint) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                                 (Etempvar _n tint) tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _t'5
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _a (tptr tdouble))
                                          (Ebinop Oadd
                                            (Ebinop Omul (Etempvar _i tint)
                                              (Etempvar _n tint) tint)
                                            (Etempvar _j tint) tint)
                                          (tptr tdouble)) tdouble))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _a (tptr tdouble))
                                          (Ebinop Oadd
                                            (Ebinop Omul (Etempvar _i tint)
                                              (Etempvar _n tint) tint)
                                            (Etempvar _j tint) tint)
                                          (tptr tdouble)) tdouble)
                                      (Ebinop Omul (Etempvar _t'5 tdouble)
                                        (Etempvar _dum tdouble) tdouble))))
                                (Sset _i
                                  (Ebinop Oadd (Etempvar _i tint)
                                    (Econst_int (Int.repr 1) tint) tint)))))
                          Sskip)))))))))
        (Sset _j
          (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
            tint))))))
|}.

Definition composites : list composite_definition :=
(Composite __1543 Struct
   (Member_plain _m tint :: Member_plain _n tint ::
    Member_plain _a (tarray (tarray tdouble 20) 20) ::
    Member_plain _ap (tptr tdouble) :: nil)
   noattr :: nil).

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
     cc_default)) :: (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
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
 (_fabs,
   Gfun(External (EF_external "fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_Matrix_Error, Gfun(Internal f_Matrix_Error)) ::
 (_axb, Gfun(Internal f_axb)) :: (_lu_bksb, Gfun(Internal f_lu_bksb)) ::
 (_ainv, Gfun(Internal f_ainv)) :: (_lu_dcmp, Gfun(Internal f_lu_dcmp)) ::
 nil).

Definition public_idents : list ident :=
(_lu_dcmp :: _ainv :: _lu_bksb :: _axb :: _printf :: _fabs ::
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


