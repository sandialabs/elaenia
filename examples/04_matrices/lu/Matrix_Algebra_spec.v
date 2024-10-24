Require Import VST.floyd.proofauto.
Require Import Matrix_Algebra.
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

Global Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition TMatrix_MxN := Eval compute in match (nth 0 composites default) with
                                          | Composite x Struct _ y => (Tstruct x y)
                                          | _ => (Tunion 1%positive noattr)
                                          end.

(* Here is where it would be nice to see the implementation specific details for matricies
   as I believe we will need a way to convert back and forth to truely give the proper spec. *)

Notation MAX_N := 20%nat.

Definition list_list_max {A : Type} (ll : list (list A)) :=
  fold_right (fun l acc => Nat.max (length l) acc) 0%nat ll.

Definition matrix_m_size {A : Type} (ll : list (list A)) (max : nat) : nat := Nat.min (length ll) max.
Definition matrix_n_size {A : Type} (ll : list (list A)) (max : nat) : nat := Nat.min (list_list_max ll) max.

Lemma matrix_m_size_MAX {A : Type} (ll : list (list A)) (max : nat) : Nat.leb (matrix_m_size ll max) max = true.
Proof. unfold matrix_m_size; rewrite Nat.leb_le; apply Nat.le_min_r. Qed.

Lemma matrix_n_size_MAX {A : Type} (ll : list (list A)) (max : nat) : Nat.leb (matrix_n_size ll max) max = true.
Proof. unfold matrix_n_size; rewrite Nat.leb_le; apply Nat.le_min_r. Qed.

Record IRMatrix_MxN :=
  {
    matrix_data :> list (list float);
    matrix_m : nat;
    matrix_n : nat;
    max_m : Nat.leb matrix_m MAX_N = true;
    max_n : Nat.leb matrix_n MAX_N = true;
    max_data : (andb (forallb (fun x => Nat.eqb (length x) MAX_N) matrix_data)
                     (Nat.eqb (length matrix_data) MAX_N)) = true
  }.

Definition IRMatrix_matrix (i : IRMatrix_MxN) : list (list float) :=
  let m := matrix_m i in
  let n := matrix_n i in
  let d := matrix_data i in
  fold_right (fun l acc => firstn m l :: acc) nil (firstn n d).

Definition ap := Vundef.  (* This, supposedly, isn't doing much of anything *)

Record VMatrix_MxN :=
  {
    vmatrix_data :> list (list val);
    vmatrix_m : val;
    vmatrix_n : val;
    vmax_data : (andb (forallb (fun x => Nat.eqb (length x) MAX_N) vmatrix_data)
                     (Nat.eqb (length vmatrix_data) MAX_N)) = true
  }.

Lemma IRMatrix_max_vmax (m : IRMatrix_MxN) :
  andb (forallb (fun x => Nat.eqb (length x) MAX_N) (map (map Vfloat) (matrix_data m)))
       (Nat.eqb (length (map (map Vfloat) (matrix_data m))) MAX_N) = true.
Proof.
  destruct m; cbn in *; rewrite andb_true_iff in *; destruct max_data0 as (P & P0); split.
  - rewrite forallb_forall in *; intros.
    rewrite in_map_iff in H; destruct H as (x' & P1 & P2); subst.
    rewrite map_length.
    specialize (P _ P2); assumption.
  - rewrite map_length; assumption.
Qed.

Definition IRMatrix_VMatrix (m : IRMatrix_MxN) : VMatrix_MxN :=
  Build_VMatrix_MxN
    (map (map Vfloat) (matrix_data m))
    (Vint (Int.repr (Z.of_nat (matrix_m m))))
    (Vint (Int.repr (Z.of_nat (matrix_n m))))
    (IRMatrix_max_vmax m).

Definition VMatrix_MMatrix (sh : share) (vm : VMatrix_MxN) (v : val) : mpred :=
  data_at sh TMatrix_MxN (vmatrix_m vm, (vmatrix_n vm, (vmatrix_data vm, ap))) v.

Definition VMatrix_default : VMatrix_MxN :=
  Build_VMatrix_MxN
    (repeat (repeat Vundef MAX_N) MAX_N)
    Vundef
    Vundef
    ltac:(cbn; auto).

Lemma matrix_max (ll : list (list float)) : andb (Nat.leb (matrix_m_size ll MAX_N) MAX_N)
                                                 (Nat.leb (matrix_n_size ll MAX_N) MAX_N) = true.
Proof. rewrite matrix_m_size_MAX, matrix_n_size_MAX; reflexivity. Qed.

Definition list_resize {A : Type} (size : nat) (a : A) (l : list A) : list A :=
  (firstn size l) ++ (repeat a (size - length l)%nat).

Lemma list_resize_length {A : Type} (size : nat) :
  forall (a : A) (l : list A),
    length (list_resize size a l) = size.
Proof. intros; unfold list_resize; rewrite app_length, firstn_length, repeat_length; lia. Qed.

Definition Matrix_resize (ll : list (list float)) : list (list float) :=
  list_resize MAX_N (repeat default MAX_N) (map (list_resize MAX_N default) ll).

Lemma Matrix_resize_max (ll : list (list float)) :
  let matrix_data := Matrix_resize ll in
  andb (forallb (fun x => Nat.eqb (length x) MAX_N) matrix_data)
       (Nat.eqb (length matrix_data) MAX_N) = true.
Proof.
  rewrite andb_true_iff; split.
  - unfold Matrix_resize.
    rewrite forallb_forall; intros.
    unfold list_resize at 1 in H.
    rewrite in_app_iff in H; destruct H.
    + apply firstn_In, in_map_iff in H.
      destruct H as (y & P & P0).
      rewrite <- P, list_resize_length.
      apply Nat.eqb_refl.
    + apply repeat_spec in H; rewrite H, repeat_length.
      apply Nat.eqb_refl.
  - unfold Matrix_resize.
    rewrite list_resize_length.
    apply Nat.eqb_refl.
Qed.

Definition Matrix_Error_spec : ident * funspec :=
DECLARE _Matrix_Error
  WITH sh: share, size : Z, str : list val, p : val
  PRE [tptr tschar]
  PROP (readable_share sh; Zlength str = size)
  PARAMS (p)
  SEP (data_at sh (tarray tschar size) str p)
  POST [tvoid]
  PROP()
  RETURN ()
  SEP (data_at sh (tarray tschar size) str p).

Definition entry {A : Type} (ll : list (list A)) (n m : nat) (d : A) : A := nth n (nth m ll nil) d.
Definition f0 : float := Float.of_bits (Int64.repr 0).
Definition update_list_list {A : Type} (ll : list (list A)) (n m : nat) (v : A) (def : list A) : list (list A) :=
  if (andb (Nat.ltb n (length ll)) (Nat.ltb m (length (nth n ll def))))
  then (replace_nth n ll (replace_nth m (nth n ll def) v))
  else ll.

Lemma replace_nth_nil {A : Type} (n : nat) (a : A) :
  replace_nth n [] a = [].
Proof. destruct n; auto. Qed.

Lemma replace_nth_length1 {A : Type} (l : list A):
  forall (n : nat) (a : A),
    length (replace_nth n l a) = length l.
Proof.
  induction l; cbn; intros.
  - rewrite replace_nth_nil; reflexivity.
  - destruct n; cbn; auto.
Qed.

Lemma in_replace_n {A : Type} :
  forall (n : nat) (a x : A) (l : list A),
    In x (replace_nth n l a) ->
    x = a \/ In x l.
Proof.
  induction n; cbn; intros; destruct l; auto.
  - destruct H; subst; auto.
    right; cbn; auto.
  - cbn in *; destruct H; auto.
    destruct (IHn _ _ _ H); auto.
Qed.

Lemma update_list_list_max {A : Type} (li : list (list A)) (n m : nat) (v : A) (def : list A)
      (max_data_li : andb (forallb (fun x => Nat.eqb (length x) MAX_N) li)
                          (Nat.eqb (length li) MAX_N) = true) :
  let lr := update_list_list li n m v def in
  andb (forallb (fun x => Nat.eqb (length x) MAX_N) lr)
       (Nat.eqb (length lr) MAX_N) = true.
Proof.
  intros; rewrite andb_true_iff.
  specialize (max_data_li) as P; rewrite andb_true_iff in P; destruct P as (P & P0).
  rewrite forallb_forall in P; split.
  - rewrite forallb_forall; intros.
    unfold lr, update_list_list in H.
    destruct Nat.ltb eqn:G in H; destruct Nat.ltb eqn:G0 in H; cbn [andb] in *;
      repeat rewrite Nat.ltb_lt in *; repeat rewrite Nat.ltb_ge in *; try (specialize (P _ H); auto).
    apply in_replace_n in H.
    destruct H as [P1|P1].
    + subst; rewrite replace_nth_length1.
      specialize (P _ (@nth_In _ n li def G)); assumption.
    + specialize (P _ P1); assumption.
  - unfold lr, update_list_list.
    destruct andb eqn:G in |-*; [rewrite replace_nth_length1|]; auto.
Qed.

Definition update (i : IRMatrix_MxN) (n m : nat) (v : float) : IRMatrix_MxN :=
  Build_IRMatrix_MxN
    (update_list_list i n m v default)
    (matrix_m i)
    (matrix_n i)
    (max_m i)
    (max_n i)
    (update_list_list_max i n m v default (max_data i)).

Definition vupdate (vm : VMatrix_MxN) (n m : nat) (v : float) : VMatrix_MxN :=
  Build_VMatrix_MxN
    (update_list_list vm n m (Vfloat v) default)
    (vmatrix_m vm)
    (vmatrix_n vm)
    (update_list_list_max vm n m (Vfloat v) default (vmax_data vm)).

Definition vupdate_dim (vm : VMatrix_MxN) (m n : nat) : VMatrix_MxN :=
  Build_VMatrix_MxN (vmatrix_data vm) (Vint (Int.repr (Z.of_nat m))) (Vint (Int.repr (Z.of_nat n))) (vmax_data vm).

Definition vfloat_float (v : val) : float :=
  match v with
  | Vfloat f => f
  | _ => f0
  end.

Definition VMatrix_init_part2 (init_vm : VMatrix_MxN) (j k0 : nat) : VMatrix_MxN :=
  fold_left (fun acc2 k => vupdate acc2 j k f0) (seq 0 k0) init_vm.

Lemma VMatrix_init2_m (j k : nat) :
  forall (vm : VMatrix_MxN),
    vmatrix_m (VMatrix_init_part2 vm j k) = vmatrix_m vm.
Proof.
  induction k; intros; auto.
  unfold VMatrix_init_part2 in *; rewrite seq_S, fold_left_app; cbn; auto.
Qed.

Lemma VMatrix_init2_n (j k : nat) :
  forall (vm : VMatrix_MxN),
    vmatrix_n (VMatrix_init_part2 vm j k) = vmatrix_n vm.
Proof.
  induction k; intros; auto.
  unfold VMatrix_init_part2 in *; rewrite seq_S, fold_left_app; cbn; auto.
Qed.

Definition VMatrix_init_part1 (init_vm : VMatrix_MxN) (j0 : nat) : VMatrix_MxN :=
  fold_left (fun acc1 j => VMatrix_init_part2 acc1 j MAX_N) (seq 0 j0) init_vm.

Lemma VMatrix_init1_m (j : nat) :
  forall (vm : VMatrix_MxN),
    vmatrix_m (VMatrix_init_part1 vm j) = vmatrix_m vm.
Proof.
  induction j; intros; auto.
  unfold VMatrix_init_part1 in *; rewrite seq_S, fold_left_app; cbn [Nat.add fold_left].
  rewrite VMatrix_init2_m, IHj; reflexivity.
Qed.

Lemma VMatrix_init1_n (j : nat) :
  forall (vm : VMatrix_MxN),
    vmatrix_n (VMatrix_init_part1 vm j) = vmatrix_n vm.
Proof.
  induction j; intros; auto.
  unfold VMatrix_init_part1 in *; rewrite seq_S, fold_left_app; cbn [Nat.add fold_left].
  rewrite VMatrix_init2_n, IHj; reflexivity.
Qed.

Definition IRMatrix_mult_part3 (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN) (r c i0 : nat) : VMatrix_MxN :=
  fold_left (fun acc3 i =>
               (vupdate acc3 r c
                        ((vfloat_float (entry acc3 c r Vundef))
                         + (entry m1 i r default) * (entry m2 c i default))%F64))
            (seq 0 i0) (vupdate init_vm r c f0).
                               

Definition IRMatrix_mult_part2 (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN) (r c0 : nat) : VMatrix_MxN :=
  fold_left (fun acc2 c => IRMatrix_mult_part3 m1 m2 acc2 r c (matrix_n m1)) (seq 0 c0) init_vm.
                               
Definition IRMatrix_mult_part1 (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN) (r0 : nat) : VMatrix_MxN :=
  fold_left (fun acc1 r => IRMatrix_mult_part2 m1 m2 acc1 r (matrix_n m2))
            (seq 0 r0) (vupdate_dim init_vm (matrix_m m1) (matrix_n m2)).

Lemma IRMatrix_mult_part3_m (r c i0 : nat) :
  forall (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN),
    let AxB_3 := IRMatrix_mult_part3 m1 m2 init_vm r c i0 in
    vmatrix_m AxB_3 = vmatrix_m init_vm.
Proof.
  induction i0; intros.
  - cbn; auto.
  - unfold AxB_3, IRMatrix_mult_part3 in *; rewrite seq_S, fold_left_app; cbn.
    rewrite IHi0; auto.
Qed.

Lemma IRMatrix_mult_part3_n (r c i0 : nat) :
  forall (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN),
    let AxB_3 := IRMatrix_mult_part3 m1 m2 init_vm r c i0 in
    vmatrix_n AxB_3 = vmatrix_n init_vm.
Proof.
  induction i0; intros.
  - cbn; auto.
  - unfold AxB_3, IRMatrix_mult_part3 in *; rewrite seq_S, fold_left_app; cbn.
    rewrite IHi0; auto.
Qed.

Lemma IRMatrix_mult_part2_m (r c0 : nat) :
  forall (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN),
    let AxB_2 := IRMatrix_mult_part2 m1 m2 init_vm r c0 in
    vmatrix_m AxB_2 = vmatrix_m init_vm.
Proof.
  induction c0; intros.
  - cbn; auto.
  - unfold AxB_2, IRMatrix_mult_part2 in *; rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
    rewrite IRMatrix_mult_part3_m; auto.
Qed.

Lemma IRMatrix_mult_part2_n (r c0 : nat) :
  forall (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN),
    let AxB_2 := IRMatrix_mult_part2 m1 m2 init_vm r c0 in
    vmatrix_n AxB_2 = vmatrix_n init_vm.
Proof.
  induction c0; intros.
  - cbn; auto.
  - unfold AxB_2, IRMatrix_mult_part2 in *; rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
    rewrite IRMatrix_mult_part3_n; auto.
Qed.

Lemma IRMatrix_mult_part1_m (r0 : nat) :
  forall (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN),
    let AxB_1 := IRMatrix_mult_part1 m1 m2 init_vm r0 in
    vmatrix_m AxB_1 = Vint (Int.repr (Z.of_nat (matrix_m m1))).
Proof.
  induction r0; intros.
  - cbn; auto.
  - unfold AxB_1, IRMatrix_mult_part1 in *; rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
    rewrite IRMatrix_mult_part2_m; auto.
Qed.

Lemma IRMatrix_mult_part1_n (r0 : nat) :
  forall (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN),
    let AxB_1 := IRMatrix_mult_part1 m1 m2 init_vm r0 in
    vmatrix_n AxB_1 = Vint (Int.repr (Z.of_nat (matrix_n m2))).
Proof.
  induction r0; intros.
  - cbn; auto.
  - unfold AxB_1, IRMatrix_mult_part1 in *; rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
    rewrite IRMatrix_mult_part2_n; auto.
Qed.

Lemma nth_replace_nth {A : Type} (l : list A) (v d : A) :
  forall (m : nat),
    (m < length l)%nat ->
    nth m (replace_nth m l v) d = v.
Proof.
  induction l; intros.
  - cbn in H; lia.
  - destruct m; cbn; auto.
    apply IHl; cbn in H; lia.
Qed.

Lemma nth_replace_nth_neq {A : Type} (l : list A) (v d : A) :
  forall (m n : nat),
    (n < length l)%nat ->
    (m <> n)%nat ->
    nth m (replace_nth n l v) d = nth m l d.
Proof.
  induction l; intros.
  - cbn in H; lia.
  - destruct n, m; cbn; try lia; auto.
    cbn in H.
    rewrite IHl; auto; lia.
Qed.

Lemma init_to_zero2 (init_vm : VMatrix_MxN) (c0 : nat) :
  forall r0 r c d1 d2,
    (r0 <= r < MAX_N)%nat ->
    (c0 <= c < MAX_N)%nat ->
    (forall d1' d2', nth c (nth r init_vm d1') d2' = Vfloat f0) ->
    nth c (nth r (VMatrix_init_part2 init_vm r0 c0) d1) d2 = Vfloat f0.
Proof.
  induction c0; intros.
  - cbn; auto.
  - unfold VMatrix_init_part2 in *; rewrite seq_S, fold_left_app; cbn.
    unfold update_list_list.
    set (init1 := fold_left (fun acc2 k => vupdate acc2 r0 k f0) (seq 0 c0) init_vm) in *.
    specialize (vmax_data init1) as P.
    rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P; setoid_rewrite Nat.eqb_eq in P.
    destruct P as (P & P0).
    repeat (let G := fresh "G" in destruct Nat.ltb eqn:G; [rewrite Nat.ltb_lt in G|rewrite Nat.ltb_ge in G]); cbn; try lia.
    + destruct (Nat.eq_dec r r0), (Nat.eq_dec c c0); subst; rewrite ?nth_replace_nth; auto;
        rewrite ?nth_replace_nth_neq; auto; try lia.
      * apply IHc0; auto; lia.
      * apply IHc0; auto; lia.
    + rewrite P in G0; [|apply nth_In]; lia.
Qed.
      
Lemma nth_vupdate (init_vm : VMatrix_MxN) (d1 : list val) (d2 : val) (f : float) :
  forall (r c : nat),
    (r < MAX_N)%nat ->
    (c < MAX_N)%nat ->
    nth c (nth r (vupdate init_vm r c f) d1) d2 = Vfloat f.
Proof.
  unfold vupdate; cbn; unfold update_list_list; intros.
  specialize (vmax_data init_vm) as P.
  rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P; destruct P as (P & P0).
  setoid_rewrite Nat.eqb_eq in P.
  repeat let G := fresh "G" in destruct Nat.ltb eqn:G in |-*;
                               repeat rewrite Nat.ltb_lt in *; repeat rewrite Nat.ltb_ge in *; cbn [andb]; try lia.
  - rewrite ?nth_replace_nth; auto.
  - rewrite P in G0; [|apply nth_In]; lia.
Qed.
  
Lemma IRMatrix_mult3_is_float (i0 : nat) :
  forall (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN) (r c : nat) (d1 : list val) (d2 : val),
    (r < MAX_N)%nat ->
    (c < MAX_N)%nat ->
    is_float (nth c (nth r (IRMatrix_mult_part3 m1 m2 init_vm r c i0) d1) d2).
Proof.
  induction i0; intros.
  - cbn; unfold update_list_list; intros.
    specialize (vmax_data init_vm) as P; rewrite andb_true_iff in P; destruct P as (P & P0).
    rewrite Nat.eqb_eq in P0.
    rewrite forallb_forall in P.
    repeat let G := fresh "G" in destruct Nat.ltb eqn:G in |-*;
                                 repeat rewrite Nat.ltb_lt in *; repeat rewrite Nat.ltb_ge in *; cbn [andb].
    + rewrite ?nth_replace_nth; cbn; auto.
    + exfalso.
      specialize (P _ (@nth_In _ r init_vm default G)); rewrite Nat.eqb_eq in P; lia.
    + exfalso; lia.
  - intros.
    unfold IRMatrix_mult_part3 in *.
    rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
    match goal with | H: _ |- context[vupdate ?a _ _ _] => set (axb := a) in * end.
    rewrite nth_vupdate; cbn; auto.
Qed.

Lemma IRMatrix_mult3_is_float_full (i0 : nat) :
  forall (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN)
         (r c r0 c0 : nat) (d1 : list val) (d2 : val),
    (r < MAX_N)%nat ->
    (c < MAX_N)%nat ->
    (forall d1' d2', is_float (nth c (nth r init_vm d1') d2')) ->
    is_float (nth c (nth r (IRMatrix_mult_part3 m1 m2 init_vm r0 c0 i0) d1) d2).
Proof.
  induction i0; intros.
  - unfold IRMatrix_mult_part3, vupdate; cbn.
    unfold update_list_list.
    specialize (vmax_data init_vm) as P.
    rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P.
    setoid_rewrite Nat.eqb_eq in P; destruct P as (P & P0).
    repeat (let G := fresh "G" in destruct Nat.ltb eqn:G; [rewrite Nat.ltb_lt in G|rewrite Nat.ltb_ge in G]); cbn; auto.
    destruct (Nat.eq_dec r r0), (Nat.eq_dec c c0); subst; rewrite ?nth_replace_nth; try rewrite nth_replace_nth_neq; auto.
    unfold is_float; auto.
  - unfold IRMatrix_mult_part3 in *.
    rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
    unfold vupdate at 1; cbn [vmatrix_data].
    unfold update_list_list at 1.
    match goal with | H : _ |- context [Nat.ltb ?a (length (vmatrix_data ?b))] => set (init_vm' := b) in * end.
    repeat (let G := fresh "G" in destruct Nat.ltb eqn:G; [rewrite Nat.ltb_lt in G|rewrite Nat.ltb_ge in G]); cbn; auto;
      try (unfold init_vm'; eapply IHi0; eauto).
    destruct (Nat.eq_dec r r0), (Nat.eq_dec c c0); subst; rewrite ?nth_replace_nth;
      try rewrite nth_replace_nth_neq; auto; try (unfold init_vm'; eapply IHi0; eauto).
    unfold is_float; auto.
Qed.
  
Lemma IRMatrix_mult2_is_float_full (c0 : nat) :
  forall (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN) (c r r0 : nat) (d1 : list val) (d2 : val),
    (r < MAX_N)%nat ->
    (c < MAX_N)%nat ->
    (forall d1' d2', is_float (nth c (nth r init_vm d1') d2')) ->
    is_float (nth c (nth r (IRMatrix_mult_part2 m1 m2 init_vm r0 c0) d1) d2).
Proof.
  induction c0; intros.
  - cbn; unfold update_list_list; auto.
  - unfold IRMatrix_mult_part2 in *.
    rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
    apply IRMatrix_mult3_is_float_full; auto.
Qed.
  
Lemma IRMatrix_mult1_is_float_full (r0 : nat) :
  forall (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN) (c r : nat) (d1 : list val) (d2 : val),
    (r < MAX_N)%nat ->
    (c < MAX_N)%nat ->
    (forall d1' d2', is_float (nth c (nth r init_vm d1') d2')) ->
    is_float (nth c (nth r (IRMatrix_mult_part1 m1 m2 init_vm r0) d1) d2).
Proof.
  induction r0; intros.
  - cbn; unfold update_list_list; auto.
  - unfold IRMatrix_mult_part1 in *.
    rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
    apply IRMatrix_mult2_is_float_full; auto.
Qed.

Definition IRMatrix_mult (m1 m2 : IRMatrix_MxN) (init_vm : VMatrix_MxN) : VMatrix_MxN :=
  IRMatrix_mult_part1 m1 m2 init_vm (matrix_m m1).

Definition stringlit_2_vals :=
  Eval compute in
    let conv := (fun x => match x with | Init_int8 v => v | _ => default end) in
    map Vint (map conv (gvar_init v___stringlit_2)).

Definition stringlit_2_mpred (gv : globals) : mpred :=
  let rt := (gvar_info v___stringlit_2) in
  data_at Ers rt stringlit_2_vals (gv ___stringlit_2).

Lemma upd_Znth_nil {A : Type} (a : A) :
  forall n,
    upd_Znth n nil a = nil.
Proof. unfold upd_Znth; cbv; destruct n; auto. Qed.

Lemma upd_Znth_replace_nth {A : Type} (l : list A) (a : A) :
  forall n,
    upd_Znth (Z.of_nat n) l a = replace_nth n l a.
Proof.
  induction l; intros.
  - rewrite replace_nth_nil, upd_Znth_nil; reflexivity.
  - destruct n; cbn -[Z.of_nat].
    + rewrite upd_Znth0; reflexivity.
    + replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
      destruct (Z_le_lt_dec (Zlength l) (Z.of_nat n)).
      * rewrite <- IHl, ?upd_Znth_out_of_range; auto; try lia.
        rewrite Zlength_cons; lia.
      * change (a0 :: l) with ([a0] ++ l).
        rewrite upd_Znth_app2 by (cbn; lia).
        replace (1 + Z.of_nat n - Zlength [a0]) with (Z.of_nat n) by (cbn; lia); rewrite IHl; auto.
Qed.

Definition update_loop2 (vm1 vm2 : VMatrix_MxN) (j k0 : nat) : VMatrix_MxN :=
  fold_left (fun acc k => vupdate acc j k (vfloat_float (entry vm2 k j Vundef))) (seq 0 k0) vm1.

Lemma vupdate_vmatrix_n vm j k v :
  vmatrix_n (vupdate vm j k v) = vmatrix_n vm.
Proof. destruct vm; cbn in *; auto. Qed.

Lemma vupdate_vmatrix_m vm j k v :
  vmatrix_m (vupdate vm j k v) = vmatrix_m vm.
Proof. destruct vm; cbn in *; auto. Qed.

Lemma update_loop2_n (j k0 : nat) :
  forall (vm1 vm2 : VMatrix_MxN),
    vmatrix_n (update_loop2 vm1 vm2 j k0) = vmatrix_n vm1.
Proof.
  induction k0; intros; auto.
  unfold update_loop2 in *; rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
  rewrite vupdate_vmatrix_n, IHk0; reflexivity.
Qed.

Lemma update_loop2_m (j k0 : nat) :
  forall (vm1 vm2 : VMatrix_MxN),
    vmatrix_m (update_loop2 vm1 vm2 j k0) = vmatrix_m vm1.
Proof.
  induction k0; intros; auto.
  unfold update_loop2 in *; rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
  rewrite vupdate_vmatrix_m, IHk0; reflexivity.
Qed.

Lemma update_loop2_copy (j k0 : nat) :
  forall (vm1 vm2 : VMatrix_MxN) (k : nat) (d1 : list val) (d2 : val),
    (k < k0)%nat ->
    (k0 <= MAX_N)%nat ->
    (j < MAX_N)%nat ->
    nth k (nth j (update_loop2 vm1 vm2 j k0) d1) d2 = Vfloat (vfloat_float (nth k (nth j vm2 []) Vundef)).
Proof.
  induction k0; intros; try lia.
  unfold update_loop2 in *; rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
  cbn; unfold update_list_list.
  set (l2 := fold_left (fun acc k1 => vupdate acc j k1 (vfloat_float (entry vm2 k1 j Vundef))) (seq 0 k0) vm1) in *.
  specialize (vmax_data l2) as P.
  rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P.
  setoid_rewrite Nat.eqb_eq in P; destruct P as (P & P0).
  repeat let G := fresh "G" in destruct Nat.ltb eqn:G; [rewrite Nat.ltb_lt in G|rewrite Nat.ltb_ge in G];
                               cbn[andb]; try lia.
  - rewrite nth_replace_nth; auto.
    destruct (Nat.eq_dec k k0); subst.
    + rewrite nth_replace_nth; auto.
    + rewrite nth_replace_nth_neq; auto.
      unfold l2; rewrite IHk0; auto; lia.
  - rewrite P in G0; [|apply nth_In]; lia.
Qed.

Lemma update_loop2_copy_total :
  forall (vm1 vm2 : VMatrix_MxN) (j : nat) (d1 d2 : list val),
    (j < MAX_N)%nat ->
    nth j (update_loop2 vm1 vm2 j MAX_N) d1 = map (fun l => Vfloat (vfloat_float l)) (nth j vm2 d2).
Proof.
  intros.
  specialize (vmax_data (update_loop2 vm1 vm2 j MAX_N)) as P.
  rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P.
  setoid_rewrite Nat.eqb_eq in P; destruct P as (P & P0).
  specialize (vmax_data vm2) as P1.
  rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P1.
  setoid_rewrite Nat.eqb_eq in P1; destruct P1 as (P1 & P2).
  eapply nth_ext.
  - rewrite map_length, P, P1; auto; apply nth_In; lia.
  - intros; rewrite update_loop2_copy; try lia.
    + erewrite nth_map' with (d' := Vundef).
      * do 3 f_equal; apply nth_indep; lia.
      * rewrite P in H0; [|apply nth_In]; try lia.
        rewrite P1; [|apply nth_In]; lia.
    + rewrite P in H0; [|apply nth_In]; lia.
      Unshelve.
      all:exact Vundef.
Qed.

Lemma update_loop2_neq (j : nat) :
  forall (vm1 vm2 : VMatrix_MxN) (j0 k : nat) (d1 : list val),
    (j < MAX_N)%nat ->
    j <> j0 ->
    nth j0 (update_loop2 vm1 vm2 j k) d1 = nth j0 vm1 d1.
Proof.
  induction k; intros; unfold update_loop2 in *; cbn [fold_left]; auto.
  rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
  cbn; unfold update_list_list.
  repeat let G := fresh "G" in destruct Nat.ltb eqn:G; [rewrite Nat.ltb_lt in G|rewrite Nat.ltb_ge in G];
                               cbn[andb]; try lia.
  - rewrite nth_replace_nth_neq; auto.
  - apply IHk; auto.
  - unfold update_loop2; cbn; auto.
Qed.

Definition update_loop1 (vm1 vm2 : VMatrix_MxN) (j0 : nat) : VMatrix_MxN :=
  fold_left (fun acc j => update_loop2 acc vm2 j MAX_N) (seq 0 j0) vm1.

Lemma update_loop1_n (j0 : nat) :
  forall (vm1 vm2 : VMatrix_MxN),
    vmatrix_n (update_loop1 vm1 vm2 j0) = vmatrix_n vm1.
Proof.
  induction j0; intros; auto.
  unfold update_loop1.
  rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
  rewrite update_loop2_n; apply IHj0.
Qed.

Lemma update_loop1_m (j0 : nat) :
  forall (vm1 vm2 : VMatrix_MxN),
    vmatrix_m (update_loop1 vm1 vm2 j0) = vmatrix_m vm1.
Proof.
  induction j0; intros; auto.
  unfold update_loop1.
  rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
  rewrite update_loop2_m; apply IHj0.
Qed.

Lemma update_loop1_copy (j0 : nat) :
  forall (j : nat) (vm1 vm2 : VMatrix_MxN) (d1 d2 : list val),
    (j < j0)%nat ->
    (j0 <= MAX_N)%nat ->
    nth j (update_loop1 vm1 vm2 j0) d1 = map (fun l => Vfloat (vfloat_float l)) (nth j vm2 d2).
Proof.
  induction j0; intros; try lia.
  unfold update_loop1 in *; rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
  destruct (Nat.eq_dec j j0); subst.
  - erewrite update_loop2_copy_total; eauto.
  - rewrite update_loop2_neq; auto.
    apply IHj0; lia.
Qed.

Lemma update_loop1_copy_total (vm1 vm2 : VMatrix_MxN) :
  vmatrix_data (update_loop1 vm1 vm2 MAX_N) = map (map (fun l => Vfloat (vfloat_float l))) vm2.
Proof.
  specialize (vmax_data (update_loop1 vm1 vm2 MAX_N)) as P.
  rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P.
  setoid_rewrite Nat.eqb_eq in P; destruct P as (P & P0).
  specialize (vmax_data vm2) as P1.
  rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P1.
  setoid_rewrite Nat.eqb_eq in P1; destruct P1 as (P1 & P2).
  eapply nth_ext with (d := nil) (d' := nil).
  - rewrite map_length; congruence.
  - intros.
    change nil with (map (fun l => Vfloat (vfloat_float l)) nil) at 2.
    rewrite map_nth.
    apply update_loop1_copy; auto.
    rewrite P0 in H; auto.
Qed.

Lemma Vfloat_vfloat_float_id (v : val):
  is_float v ->
  Vfloat (vfloat_float v) = v.
Proof. intros; destruct v; try contradiction; reflexivity. Qed.

Lemma Forall_is_float (vm1 vm2 : VMatrix_MxN) :
  Forall (Forall is_float) vm2 ->
  vmatrix_data (update_loop1 vm1 vm2 MAX_N) = vmatrix_data vm2.
Proof.
  intros.
  rewrite update_loop1_copy_total.
  rewrite (@map_ext_Forall _ _ (map (fun l => Vfloat (vfloat_float l))) id (vmatrix_data vm2)), map_id_eq; auto.
  induction (vmatrix_data vm2); auto.
  inversion H; subst; econstructor.
  - cbn.
    clear - H2.
    induction a; auto; inversion H2; subst.
    cbn; rewrite Vfloat_vfloat_float_id; auto.
    rewrite IHa; auto.
  - apply IHl; auto.
Qed.

Definition axb_spec : ident * funspec :=
DECLARE _axb
  WITH ash: share, bsh: share, csh : share, air : IRMatrix_MxN, bir : IRMatrix_MxN, cir : VMatrix_MxN,
       ap : val, bp : val, cp : val, gv : globals
  PRE [tptr TMatrix_MxN, tptr TMatrix_MxN, tptr TMatrix_MxN]
  PROP (readable_share ash; readable_share bsh; writable_share csh)
  PARAMS (ap; bp; cp)
  GLOBALS (gv)
  SEP (VMatrix_MMatrix ash (IRMatrix_VMatrix air) ap;
       VMatrix_MMatrix bsh (IRMatrix_VMatrix bir) bp;
       VMatrix_MMatrix csh cir cp; stringlit_2_mpred gv)
  POST [tvoid]
  EX ret1 : VMatrix_MxN,
  PROP (ret1 = IRMatrix_mult air bir (VMatrix_init_part1 VMatrix_default 20))
  RETURN ()
  SEP (VMatrix_MMatrix ash (IRMatrix_VMatrix air) ap;
       VMatrix_MMatrix bsh (IRMatrix_VMatrix bir) bp;
       VMatrix_MMatrix csh ret1 cp; stringlit_2_mpred gv).

Definition Gprog := [Matrix_Error_spec; axb_spec].

Lemma body_axb : semax_body Vprog Gprog f_axb axb_spec.
Proof.
  start_function.
  specialize (max_m air) as P; rewrite Nat.leb_le in P.
  specialize (max_n bir) as P0; rewrite Nat.leb_le in P0.
  specialize (max_n air) as P1; rewrite Nat.leb_le in P1.
  forward_for_simple_bound
    20
    (EX j : Z,
        PROP ( )
             LOCAL (lvar _ret (Tstruct __1596 noattr) v_ret; 
                    gvars gv; temp _a ap; temp _b bp; temp _C cp)
             SEP (VMatrix_MMatrix Tsh (VMatrix_init_part1 VMatrix_default (Z.to_nat j)) v_ret;
                  VMatrix_MMatrix ash (IRMatrix_VMatrix air) ap;
                  VMatrix_MMatrix bsh (IRMatrix_VMatrix bir) bp;
                  VMatrix_MMatrix csh cir cp; stringlit_2_mpred gv)).
  - entailer!.
    rewrite data_at__eq; cbn.
    unfold VMatrix_MMatrix; entailer!.
  - forward_for_simple_bound
      20
      (EX k : Z,
          EX vm : VMatrix_MxN,
            PROP (vm = VMatrix_init_part1 VMatrix_default (Z.to_nat i))
                 LOCAL (temp _j (Vint (Int.repr i));
                        lvar _ret (Tstruct __1596 noattr) v_ret; gvars gv; 
                        temp _a ap; temp _b bp; temp _C cp)
                 SEP (VMatrix_MMatrix Tsh (VMatrix_init_part2 vm (Z.to_nat i) (Z.to_nat k)) v_ret;
                      VMatrix_MMatrix ash (IRMatrix_VMatrix air) ap;
                      VMatrix_MMatrix bsh (IRMatrix_VMatrix bir) bp;
                      VMatrix_MMatrix csh cir cp; stringlit_2_mpred gv)).
    + Exists (VMatrix_init_part1 VMatrix_default (Z.to_nat i)).
      entailer!.
      unfold VMatrix_init_part2; cbn [Z.to_nat seq fold_left]; entailer!.
    + unfold VMatrix_MMatrix; forward.
      Exists vm.
      entailer!.
      unfold VMatrix_MMatrix.
      rewrite ?VMatrix_init2_m, VMatrix_init1_m, ?VMatrix_init2_n, VMatrix_init1_n.
      replace i with (Z.of_nat (Z.to_nat i)) at 1 4 by lia.
      replace i0 with (Z.of_nat (Z.to_nat i0)) at 2 by lia.
      replace (Z.to_nat (i0 + 1)) with (S (Z.to_nat i0)) by lia.
      unfold VMatrix_init_part2.
      rewrite ?upd_Znth_replace_nth, seq_S, fold_left_app; cbn [fold_left Nat.add vmatrix_data vmatrix_m vmatrix_n].
      rewrite ?vupdate_vmatrix_n, ?vupdate_vmatrix_m, <- ?nth_Znth'; cbn.
      unfold update_list_list.
      let P := fresh "P" in
      match goal with | H : _ |- context [Nat.ltb ?x (length (vmatrix_data ?a))]
                        => set (inits := a) in *; specialize (vmax_data inits) as P end.
      rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P2.
      setoid_rewrite Nat.eqb_eq in P2; destruct P2 as (P2 & P3).
      destruct Nat.ltb eqn:G; [rewrite Nat.ltb_lt in G|rewrite Nat.ltb_ge in G; lia].
      destruct Nat.ltb eqn:G0; [rewrite Nat.ltb_lt in G0|rewrite Nat.ltb_ge in G0; rewrite P2 in G0; [|apply nth_In]; lia].
      cbn [andb].
      unfold default, Inhabitant_list.
      erewrite nth_indep; try entailer!; lia.
    + replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      Intros vm.
      subst; unfold VMatrix_init_part1; rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
      change (Z.to_nat 20) with 20%nat.
      entailer!.
  - repeat forward.
    forward_if True.
    + forward_call (Ers, 34, stringlit_2_vals, (gv ___stringlit_2) ); [unfold stringlit_2_mpred; entailer!| entailer!].
    + forward; entailer!.
    + Intros.
      forward.
      forward_loop
        (EX r : Z,
            EX vm : VMatrix_MxN,
              PROP (
                  0 <= r <= Z.of_nat (matrix_m air);
                  vm = VMatrix_init_part1 VMatrix_default MAX_N
                )
                   LOCAL (gvars gv;
                          temp _r (Vint (Int.repr r));
                          temp _t'11 (Vint (Int.repr (Z.of_nat (matrix_m bir))));
                          temp _t'10 (Vint (Int.repr (Z.of_nat (matrix_n air))));
                          temp _t'12 (Vint (Int.repr (Z.of_nat (matrix_n bir))));
                          temp _t'13 (Vint (Int.repr (Z.of_nat (matrix_m air))));
                          lvar _ret (Tstruct __1596 noattr) v_ret;  
                          temp _a ap; temp _b bp; temp _C cp)
                   SEP (VMatrix_MMatrix Tsh (IRMatrix_mult_part1 air bir vm (Z.to_nat r)) v_ret;
                        VMatrix_MMatrix ash (IRMatrix_VMatrix air) ap;
                        VMatrix_MMatrix bsh (IRMatrix_VMatrix bir) bp;
                        VMatrix_MMatrix csh cir cp;
                        stringlit_2_mpred gv)
        )
        break:
        (EX vm : VMatrix_MxN,
            PROP (vm = VMatrix_init_part1 VMatrix_default MAX_N)
                 LOCAL (temp _r (Vint (Int.repr (Z.of_nat (matrix_m air))));
                        temp _t'11 (Vint (Int.repr (Z.of_nat (matrix_m bir))));
                        temp _t'10 (Vint (Int.repr (Z.of_nat (matrix_n air))));
                        temp _t'12 (Vint (Int.repr (Z.of_nat (matrix_n bir))));
                        temp _t'13 (Vint (Int.repr (Z.of_nat (matrix_m air))));
                        lvar _ret (Tstruct __1596 noattr) v_ret; gvars gv; 
                        temp _a ap; temp _b bp; temp _C cp)
                 SEP (VMatrix_MMatrix Tsh (IRMatrix_mult air bir vm) v_ret;
                      VMatrix_MMatrix ash (IRMatrix_VMatrix air) ap;
                      VMatrix_MMatrix bsh (IRMatrix_VMatrix bir) bp;
                      VMatrix_MMatrix csh cir cp;
                      stringlit_2_mpred gv)
        ).
      * Exists 0 (VMatrix_init_part1 VMatrix_default MAX_N).
        change (Z.to_nat 20) with 20%nat.
        unfold IRMatrix_mult_part1; cbn [Z.to_nat seq fold_left].
        unfold VMatrix_MMatrix; cbn [vupdate_dim vmatrix_m vmatrix_n vmatrix_data].
        entailer!.
      * Intros r vm.
        forward.
        forward_if.
        -- forward.
           forward_loop
             (EX c : Z,
                 EX vm0 : VMatrix_MxN,
                   PROP (0 <= c <= Z.of_nat (matrix_n bir);
                         vm0 = IRMatrix_mult_part1 air bir vm (Z.to_nat r))
                        LOCAL (gvars gv;
                               temp _c (Vint (Int.repr c));
                               temp _r (Vint (Int.repr r));
                               temp _t'11 (Vint (Int.repr (Z.of_nat (matrix_m bir))));
                               temp _t'10 (Vint (Int.repr (Z.of_nat (matrix_n air))));
                               temp _t'12 (Vint (Int.repr (Z.of_nat (matrix_n bir))));
                               temp _t'13 (Vint (Int.repr (Z.of_nat (matrix_m air))));
                               lvar _ret (Tstruct __1596 noattr) v_ret;  
                               temp _a ap; temp _b bp; temp _C cp)
                        SEP (VMatrix_MMatrix Tsh (IRMatrix_mult_part2 air bir vm0 (Z.to_nat r) (Z.to_nat c)) v_ret;
                             VMatrix_MMatrix ash (IRMatrix_VMatrix air) ap;
                             VMatrix_MMatrix bsh (IRMatrix_VMatrix bir) bp;
                             VMatrix_MMatrix csh cir cp;
                             stringlit_2_mpred gv))
             break:
             (EX vm0 : VMatrix_MxN,
                 PROP (vm0 = IRMatrix_mult_part1 air bir vm (Z.to_nat r))
                      LOCAL (
                        temp _c (Vint (Int.repr (Z.of_nat (matrix_n bir))));
                        temp _r (Vint (Int.repr r));
                        temp _t'11 (Vint (Int.repr (Z.of_nat (matrix_m bir))));
                        temp _t'10 (Vint (Int.repr (Z.of_nat (matrix_n air))));
                        temp _t'12 (Vint (Int.repr (Z.of_nat (matrix_n bir))));
                        temp _t'13 (Vint (Int.repr (Z.of_nat (matrix_m air))));
                        lvar _ret (Tstruct __1596 noattr) v_ret; gvars gv; 
                        temp _a ap; temp _b bp; temp _C cp)
                      SEP (VMatrix_MMatrix Tsh (IRMatrix_mult_part2 air bir vm0 (Z.to_nat r) (matrix_n bir)) v_ret;
                           VMatrix_MMatrix ash (IRMatrix_VMatrix air) ap;
                           VMatrix_MMatrix bsh (IRMatrix_VMatrix bir) bp;
                           VMatrix_MMatrix csh cir cp;
                           stringlit_2_mpred gv)).
           ++ Exists 0 (IRMatrix_mult_part1 air bir vm (Z.to_nat r)).
              entailer!.
              unfold IRMatrix_mult_part2; cbn [Z.to_nat seq fold_left].
              entailer!.
           ++ Intros c vm0.
              forward.
              forward_if.
              ** unfold VMatrix_MMatrix.
                 repeat forward.
                 forward_loop
                   (EX i : Z,
                       EX vm1 : VMatrix_MxN,
                         PROP (
                             0 <= i <= Z.of_nat (matrix_n air);
                             vm1 = IRMatrix_mult_part2 air bir vm0 (Z.to_nat r) (Z.to_nat c)
                           )
                              LOCAL (gvars gv;
                                     temp _c (Vint (Int.repr c));
                                     temp _r (Vint (Int.repr r));
                                     temp _i (Vint (Int.repr i));
                                     temp _t'11 (Vint (Int.repr (Z.of_nat (matrix_m bir))));
                                     temp _t'10 (Vint (Int.repr (Z.of_nat (matrix_n air))));
                                     temp _t'12 (Vint (Int.repr (Z.of_nat (matrix_n bir))));
                                     temp _t'13 (Vint (Int.repr (Z.of_nat (matrix_m air))));
                                     lvar _ret (Tstruct __1596 noattr) v_ret;  
                                     temp _a ap; temp _b bp; temp _C cp)
                              SEP (VMatrix_MMatrix Tsh (IRMatrix_mult_part3
                                                          air bir vm1
                                                          (Z.to_nat r)
                                                          (Z.to_nat c)
                                                          (Z.to_nat i)) v_ret;
                                   VMatrix_MMatrix ash (IRMatrix_VMatrix air) ap;
                                   VMatrix_MMatrix bsh (IRMatrix_VMatrix bir) bp;
                                   VMatrix_MMatrix csh cir cp;
                                   stringlit_2_mpred gv))
                   break:
                   (EX vm1 : VMatrix_MxN,
                       PROP (vm1 = IRMatrix_mult_part2 air bir vm0 (Z.to_nat r) (Z.to_nat c))
                            LOCAL (
                              temp _c (Vint (Int.repr c));
                              temp _r (Vint (Int.repr r));
                              temp _i (Vint (Int.repr (Z.of_nat (matrix_n air))));
                              temp _t'11 (Vint (Int.repr (Z.of_nat (matrix_m bir))));
                              temp _t'10 (Vint (Int.repr (Z.of_nat (matrix_n air))));
                              temp _t'12 (Vint (Int.repr (Z.of_nat (matrix_n bir))));
                              temp _t'13 (Vint (Int.repr (Z.of_nat (matrix_m air))));
                              lvar _ret (Tstruct __1596 noattr) v_ret; gvars gv; 
                              temp _a ap; temp _b bp; temp _C cp)
                            SEP (VMatrix_MMatrix Tsh (IRMatrix_mult_part3
                                                        air bir vm1
                                                        (Z.to_nat r)
                                                        (Z.to_nat c)
                                                        (matrix_n air)) v_ret;
                                 VMatrix_MMatrix ash (IRMatrix_VMatrix air) ap;
                                 VMatrix_MMatrix bsh (IRMatrix_VMatrix bir) bp;
                                 VMatrix_MMatrix csh cir cp;
                                 stringlit_2_mpred gv)).
                 --- Exists 0 (IRMatrix_mult_part2 air bir vm0 (Z.to_nat r) (Z.to_nat c)).
                     unfold IRMatrix_mult_part3, VMatrix_MMatrix.
                     cbn [Z.to_nat seq fold_left].
                     entailer!.
                     unfold vupdate, update_list_list.
                     let P := fresh "P" in
                     match goal with | H : _ |- context [andb ?a ?b] => assert (andb a b = true) as P end.
                     +++ rewrite andb_true_iff, ?Nat.ltb_lt.
                         let P := fresh "P" in
                         match goal with | H : _ |- context [vmatrix_data ?a] =>
                                             specialize (vmax_data a) as P; rewrite andb_true_iff, Nat.eqb_eq in P end.
                         destruct P2 as (P2 & P3).
                         rewrite P3; rewrite forallb_forall in P2;
                           setoid_rewrite Nat.eqb_eq in P2; rewrite P2; [split; lia|].
                         apply nth_In; rewrite P3; lia.
                     +++ cbn [vmatrix_data vmatrix_n vmatrix_m]; rewrite P2.
                         replace r with (Z.of_nat (Z.to_nat r)) at 5 8 by lia;
                           replace c with (Z.of_nat (Z.to_nat c)) at 4 by lia.
                         rewrite ?upd_Znth_replace_nth, <- ?nth_Znth'; unfold f0.
                         entailer!.
                         unfold default, Inhabitant_list; rewrite (nth_indep _ nil (repeat Vundef 20 )); [entailer!|].
                         rewrite andb_true_iff, ?Nat.ltb_lt in P2; destruct P2 as (P2 & P3); auto.
                 --- Intros i vm1.
                     forward.
                     forward_if.
                     +++ unfold IRMatrix_mult_part2, VMatrix_MMatrix.
                         forward.
                         *** entailer!.
                             replace c with (Z.of_nat (Z.to_nat c)) at 1 by lia.
                             replace r with (Z.of_nat (Z.to_nat r)) at 1 by lia.
                             rewrite <- ?nth_Znth'.
                             apply IRMatrix_mult3_is_float; lia.
                         *** forward.
                             ---- entailer!.
                                  apply (proj1 (Forall_Znth (Znth r (map (map Vfloat) air)) is_float)).
                                  ++++ clear - H H1 P.
                                       enough
                                         (forall l n,
                                             (n < length l)%nat ->
                                             Forall is_float (nth n (map (map Vfloat) l) (repeat Vundef 20))) as Q.
                                       { replace r with (Z.of_nat (Z.to_nat r)) by lia.
                                         rewrite <- nth_Znth'.
                                         apply (Q air (Z.to_nat r)).
                                         specialize (max_data air) as Q0.
                                         rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in Q0; destruct Q0 as (Q0 & Q1).
                                         lia.
                                       }
                                       clear; induction l; intros.
                                       cbn in H; lia.
                                       destruct n; cbn.
                                       **** clear - a; induction a; cbn [map]; constructor; [unfold is_float|]; auto.
                                       **** cbn [length] in H; apply IHl; lia.
                                  ++++ specialize (max_data air) as P2; rewrite andb_true_iff, Nat.eqb_eq,
                                         forallb_forall in P2.
                                       setoid_rewrite Nat.eqb_eq in P2; destruct P2 as (P2 & P3).
                                       rewrite Znth_map, Zlength_map; rewrite Zlength_correct; try rewrite P2;
                                         try rewrite P3; try lia.
                                       apply Znth_In; rewrite Zlength_correct; lia.
                             ---- forward.
                                  ++++ entailer!.
                                       apply (proj1 (Forall_Znth (Znth i (map (map Vfloat) bir)) is_float)).
                                       **** clear - H5 H7 P1.
                                            enough
                                              (forall l n,
                                                  (n < length l)%nat ->
                                                  Forall is_float (nth n (map (map Vfloat) l) (repeat Vundef 20))) as Q.
                                            { replace i with (Z.of_nat (Z.to_nat i)) by lia.
                                              rewrite <- nth_Znth'.
                                              apply (Q bir (Z.to_nat i)).
                                              specialize (max_data bir) as Q0.
                                              rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in Q0;
                                                destruct Q0 as (Q0 & Q1).
                                              lia.
                                            }
                                            clear; induction l; intros.
                                            cbn in H; lia.
                                            destruct n; cbn.
                                            ----- clear - a; induction a; cbn [map]; constructor; [unfold is_float|]; auto.
                                            ----- cbn [length] in H; apply IHl; lia.
                                       **** specialize (max_data bir) as P2; rewrite andb_true_iff, Nat.eqb_eq,
                                              forallb_forall in P2.
                                            setoid_rewrite Nat.eqb_eq in P2; destruct P2 as (P2 & P3).
                                            rewrite Znth_map, Zlength_map; rewrite Zlength_correct; try rewrite P2;
                                              try rewrite P3; try lia.
                                            apply Znth_In; rewrite Zlength_correct; lia.
                                  ++++ repeat forward.
                                       **** Exists (i + 1) vm1.
                                            entailer!.
                                            replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
                                            rewrite ?IRMatrix_mult_part3_m, ?IRMatrix_mult_part2_m, ?IRMatrix_mult_part1_m,
                                              ?IRMatrix_mult_part3_n, ?IRMatrix_mult_part2_n, ?IRMatrix_mult_part1_n.
                                            unfold IRMatrix_mult_part3.
                                            rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
                                            match goal with
                                            | H : _ |- context [upd_Znth r (vmatrix_data ?a) ?x] =>
                                                set (AxB := a) in * end.
                                            unfold vupdate, update_list_list; cbn [vmatrix_data].
                                            specialize (vmax_data AxB) as P2.
                                            rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P2.
                                            setoid_rewrite Nat.eqb_eq in P2; destruct P2 as (P2 & P3); rewrite P3.
                                            destruct Nat.ltb eqn:G;
                                              [rewrite Nat.ltb_lt in G| rewrite Nat.ltb_ge in G; lia].
                                            rewrite P2 by (apply nth_In; lia).
                                            destruct Nat.ltb eqn:G0;
                                              [rewrite Nat.ltb_lt in G0| rewrite Nat.ltb_ge in G0; lia]; cbn [andb].
                                            replace r with (Z.of_nat (Z.to_nat r)) at 1 2 3 4 by lia.
                                            replace c with (Z.of_nat (Z.to_nat c)) at 1 2 3 by lia.
                                            replace i with (Z.of_nat (Z.to_nat i)) at 1 2 by lia.
                                            rewrite ?upd_Znth_replace_nth, <- ?nth_Znth'.
                                            unfold entry.
                                            assert (exists f,
                                                       nth (Z.to_nat c) (nth (Z.to_nat r) AxB (repeat Vundef MAX_N))
                                                           Vundef = Vfloat f) as P4.
                                            {
                                              enough (is_float
                                                        (nth (Z.to_nat c)
                                                             (nth (Z.to_nat r) AxB (repeat Vundef 20)) Vundef)).
                                              { unfold is_float in H0.
                                                destruct nth eqn:G1 in H0; try contradiction.
                                                rewrite G1; eauto. }
                                              unfold AxB.
                                              fold (IRMatrix_mult_part3
                                                      air bir (IRMatrix_mult_part2
                                                                 air bir
                                                                 (IRMatrix_mult_part1 air bir VMatrix_default (Z.to_nat r))
                                                                 (Z.to_nat r) (Z.to_nat c))
                                                      (Z.to_nat r) (Z.to_nat c) (Z.to_nat i)).
                                              apply IRMatrix_mult3_is_float; auto.
                                            }
                                            destruct P4 as (f & P4).
                                            unfold default, Inhabitant_list.
                                            rewrite (@nth_indep _ _ (Z.to_nat r) nil (repeat Vundef MAX_N)) by lia.
                                            unfold default in *; cbn [repeat] in *.
                                            rewrite P4; cbn [vfloat_float].
                                            specialize (max_data bir) as P5.
                                            rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P5.
                                            setoid_rewrite Nat.eqb_eq in P5.
                                            destruct P5 as (P5 & P6).
                                            assert (exists f,
                                                       (nth (Z.to_nat c) (nth (Z.to_nat i) bir nil) f0) = f)
                                              as P7 by (destruct (nth (Z.to_nat i) _ _), (Z.to_nat c); cbn; eauto).
                                            destruct P7 as (f' & P7).
                                            unfold default, Inhabitant_float.
                                            specialize (@nth_indep _ (map (map Vfloat) bir)
                                                                   (Z.to_nat i) (repeat Vundef MAX_N)
                                                                   (map Vfloat nil)) as TMP.
                                            cbn [repeat] in TMP; rewrite TMP by (rewrite ?map_length; lia); clear TMP.
                                            rewrite (@nth_indep _ _ (Z.to_nat c) Vundef (Vfloat Float.zero))
                                              by (rewrite map_nth, map_length, P5; [| apply nth_In]; lia).
                                            change Float.zero with f0.
                                            rewrite ?map_nth, P7.
                                            specialize (max_data air) as P8.
                                            rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P8.
                                            setoid_rewrite Nat.eqb_eq in P8.
                                            destruct P8 as (P8 & P9).
                                            assert (exists f,
                                                       (nth (Z.to_nat i) (nth (Z.to_nat r) air nil) f0) = f)
                                              as P10 by (destruct (nth (Z.to_nat r) _ _), (Z.to_nat i); cbn; eauto).
                                            destruct P10 as (f'' & P10).
                                            specialize (@nth_indep _ (map (map Vfloat) air)
                                                                   (Z.to_nat r) (repeat Vundef MAX_N) (map Vfloat nil))
                                              as TMP.
                                            cbn [repeat] in TMP; rewrite TMP by (rewrite ?map_length; lia); clear TMP.
                                            rewrite (@nth_indep _ _ (Z.to_nat i) Vundef (Vfloat Float.zero))
                                              by (rewrite map_nth, map_length, P8; [| apply nth_In]; lia).
                                            change Float.zero with f0.
                                            rewrite ?map_nth, P10.
                                            cbn.
                                            entailer!.
                     +++ forward.
                         Exists vm1.
                         entailer!.
                         *** do 2 f_equal; lia.
                         *** replace (Z.to_nat i) with (matrix_n air) by lia; entailer!.
                 --- Intros vm1.
                     forward.
                     Exists (c + 1) vm0.
                     entailer!.
                     unfold VMatrix_MMatrix, IRMatrix_mult_part3, IRMatrix_mult_part2.
                     replace (Z.to_nat (c + 1)) with (S (Z.to_nat c)) by lia.
                     rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
                     entailer!.
              ** forward.
                 Exists vm0.
                 entailer!.
                 --- do 2 f_equal; rep_lia.
                 --- replace (Z.to_nat c) with (matrix_n bir) by lia; entailer!.
           ++ Intros vm0.
              forward.
              Exists (r + 1) vm.
              entailer!.
              unfold IRMatrix_mult_part1, IRMatrix_mult_part2.
              replace (Z.to_nat (r + 1)) with (S (Z.to_nat r)) by lia.
              rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
              entailer!.
        -- forward.
           Exists vm.
           entailer!.
           ++ do 2 f_equal; rep_lia.
           ++ replace (Z.to_nat r) with (matrix_m air) by rep_lia.
              unfold IRMatrix_mult, IRMatrix_mult_part1; entailer!.
      * Intros vm.
        forward.
        -- entailer!.
           unfold IRMatrix_mult.
           rewrite IRMatrix_mult_part1_m; auto.
        -- repeat forward.
           ++ entailer!.
              unfold IRMatrix_mult.
              rewrite IRMatrix_mult_part1_n; auto.
           ++ unfold IRMatrix_mult; rewrite IRMatrix_mult_part1_m, IRMatrix_mult_part1_n;
                cbn [sem_cast_i2i force_val cast_int_int].
              forward_for_simple_bound (Z.of_nat MAX_N)
                                       (EX j : Z,
                                           EX vm1 : VMatrix_MxN,
                                             EX vm2 : VMatrix_MxN,
                                               PROP
                                                 (
                                                   0 <= j <= Z.of_nat MAX_N;
                                                   vm1 = vupdate_dim cir (matrix_m air) (matrix_n bir);
                                                   vm2 = IRMatrix_mult air bir vm
                                                 )
                                                 LOCAL (temp _t'2 (Vint (Int.repr (Z.of_nat (matrix_n bir))));
                                                        temp _t'3 (Vint (Int.repr (Z.of_nat (matrix_m air))));
                                                        temp _r (Vint (Int.repr (Z.of_nat (matrix_m air))));
                                                        temp _t'11 (Vint (Int.repr (Z.of_nat (matrix_m bir))));
                                                        temp _t'10 (Vint (Int.repr (Z.of_nat (matrix_n air))));
                                                        temp _t'12 (Vint (Int.repr (Z.of_nat (matrix_n bir))));
                                                        temp _t'13 (Vint (Int.repr (Z.of_nat (matrix_m air))));
                                                        lvar _ret (Tstruct __1596 noattr) v_ret; gvars gv; 
                                                        temp _a ap; temp _b bp; temp _C cp)
                                                 SEP (VMatrix_MMatrix ash (IRMatrix_VMatrix air) ap;
                                                      VMatrix_MMatrix bsh (IRMatrix_VMatrix bir) bp;
                                                      VMatrix_MMatrix Tsh vm2 v_ret;
                                                      VMatrix_MMatrix csh (update_loop1 vm1 vm2 (Z.to_nat j)) cp;
                                                      stringlit_2_mpred gv)).
              ** Exists (vupdate_dim cir (matrix_m air) (matrix_n bir)) (IRMatrix_mult air bir vm).
                 unfold VMatrix_MMatrix, IRMatrix_mult; rewrite IRMatrix_mult_part1_m, IRMatrix_mult_part1_n.
                 entailer!.
              ** forward_for_simple_bound (Z.of_nat MAX_N)
                                          (EX k : Z,
                                              EX vm1 : VMatrix_MxN,
                                                EX vm2 : VMatrix_MxN,
                                                  EX vm3 : VMatrix_MxN,
                                                    PROP
                                                      (
                                                        0 <= k <= Z.of_nat MAX_N;
                                                        vm1 = vupdate_dim cir (matrix_m air) (matrix_n bir);
                                                        vm2 = IRMatrix_mult air bir vm;
                                                        vm3 = update_loop1 vm1 vm2 (Z.to_nat i)
                                                      )
                                                      LOCAL (temp _j__1 (Vint (Int.repr i));
                                                             temp _t'2 (Vint (Int.repr (Z.of_nat (matrix_n bir))));
                                                             temp _t'3 (Vint (Int.repr (Z.of_nat (matrix_m air))));
                                                             temp _r (Vint (Int.repr (Z.of_nat (matrix_m air))));
                                                             temp _t'11 (Vint (Int.repr (Z.of_nat (matrix_m bir))));
                                                             temp _t'10 (Vint (Int.repr (Z.of_nat (matrix_n air))));
                                                             temp _t'12 (Vint (Int.repr (Z.of_nat (matrix_n bir))));
                                                             temp _t'13 (Vint (Int.repr (Z.of_nat (matrix_m air))));
                                                             lvar _ret (Tstruct __1596 noattr) v_ret; gvars gv; 
                                                             temp _a ap; temp _b bp; temp _C cp)
                                                      SEP (VMatrix_MMatrix ash (IRMatrix_VMatrix air) ap;
                                                           VMatrix_MMatrix bsh (IRMatrix_VMatrix bir) bp;
                                                           VMatrix_MMatrix Tsh vm2 v_ret;
                                                           VMatrix_MMatrix csh
                                                                           (update_loop2 vm3 vm2 (Z.to_nat i) (Z.to_nat k))
                                                                           cp;
                                                           stringlit_2_mpred gv)).
                 --- Exists (vupdate_dim cir (matrix_m air) (matrix_n bir))
                            (IRMatrix_mult air bir vm)
                            (update_loop1 vm1 vm2 (Z.to_nat i)).
                     unfold VMatrix_MMatrix, IRMatrix_mult, update_loop2;
                       rewrite ?IRMatrix_mult_part1_m, ?IRMatrix_mult_part1_n.
                     cbn [Z.to_nat seq fold_left].
                     entailer!.
                     rewrite ?IRMatrix_mult_part1_m, ?IRMatrix_mult_part1_n.
                     entailer!.
                 --- unfold VMatrix_MMatrix.
                     forward.
                     +++ entailer!.
                         unfold IRMatrix_mult.
                         replace i0 with (Z.of_nat (Z.to_nat i0)) by lia.
                         replace i with (Z.of_nat (Z.to_nat i)) by lia.
                         rewrite <- ?nth_Znth'.
                         apply IRMatrix_mult1_is_float_full; try lia; intros.
                         replace (vmatrix_data (VMatrix_init_part1 VMatrix_default 20)) with
                           (repeat (repeat (Vfloat f0) MAX_N) MAX_N).
                         *** rewrite ?nth_repeat'; unfold is_float; auto; lia.
                         *** vm_compute; auto.
                     +++ forward.
                         Exists vm0 vm3 vm4.
                         entailer!.
                         unfold VMatrix_MMatrix.
                         rewrite ?update_loop2_n, ?update_loop1_n, ?update_loop2_m, ?update_loop1_m.
                         replace (Z.to_nat (i0 + 1)) with (S (Z.to_nat i0)) by lia.
                         unfold update_loop2; rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
                         replace i with (Z.of_nat (Z.to_nat i)) at 1 3 5 by lia.
                         replace i0 with (Z.of_nat (Z.to_nat i0)) at 2 4 by lia.
                         rewrite ?upd_Znth_replace_nth, <- ?nth_Znth'.
                         match goal with | H : _ |- context [replace_nth ?x (vmatrix_data ?a) ?y]
                                           => set (loop := a) in * end.
                         unfold vupdate, update_list_list; cbn [vmatrix_data].
                         specialize (vmax_data loop) as P2.
                         rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P2.
                         setoid_rewrite Nat.eqb_eq in P2; destruct P2 as (P2 & P3).
                         repeat (let G := fresh "G" in destruct Nat.ltb eqn:G;
                                                       [rewrite Nat.ltb_lt in G|rewrite Nat.ltb_ge in G]); try lia;
                           [|rewrite P2 in G0; [|apply nth_In]; lia].
                         cbn [andb].
                         unfold entry.
                         assert (exists f, nth (Z.to_nat i0)
                                               (nth (Z.to_nat i)
                                                    (IRMatrix_mult air bir (VMatrix_init_part1 VMatrix_default MAX_N)) nil)
                                               Vundef = Vfloat f) as P4.
                         { unfold IRMatrix_mult.
                           specialize (IRMatrix_mult1_is_float_full (matrix_m air) air bir
                                                                    (VMatrix_init_part1 VMatrix_default MAX_N)
                                                                    (Z.to_nat i0)
                                                                    (Z.to_nat i) nil Vundef
                                                                    ltac:(lia) ltac:(lia)) as Q.
                           assert (forall d1' d2',
                                      is_float
                                        (nth (Z.to_nat i0)
                                             (nth (Z.to_nat i)
                                                  (VMatrix_init_part1 VMatrix_default MAX_N) d1')
                                             d2')) as Q0.
                           { intros; replace (vmatrix_data (VMatrix_init_part1 VMatrix_default 20)) with
                               (repeat (repeat (Vfloat f0) MAX_N) MAX_N).
                             - rewrite ?nth_repeat'; unfold is_float; auto; lia.
                             - vm_compute; auto.
                           }
                           specialize (Q Q0).
                           unfold is_float in Q.
                           destruct nth eqn:G1 in Q; try contradiction.
                           rewrite G1; eexists; eauto.
                         }
                         destruct P4 as (f & P4); rewrite P4.
                         unfold default.
                         specialize (vmax_data (IRMatrix_mult air bir (VMatrix_init_part1 VMatrix_default MAX_N)))
                           as P5.
                         rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P5.
                         setoid_rewrite Nat.eqb_eq in P5; destruct P5 as (P5 & P6).
                         rewrite (nth_indep _ nil (repeat Vundef MAX_N)) in P4 by lia.
                         cbn [repeat] in P4; rewrite P4.
                         unfold Inhabitant_list.
                         rewrite (nth_indep _ nil (repeat Vundef MAX_N)) by auto.
                         cbn; entailer!.
                 --- Intros vm0 vm3 vm4.
                     Exists vm0 vm3.
                     entailer!.
                     replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
                     unfold update_loop1.
                     rewrite seq_S, fold_left_app; cbn [fold_left Nat.add].
                     set (AxB := IRMatrix_mult air bir (VMatrix_init_part1 VMatrix_default MAX_N)).
                     change (Z.to_nat (Z.of_nat MAX_N)) with MAX_N.
                     cbn [fold_left].
                     entailer!.
              ** Intros vm1 vm2.
                 Exists (IRMatrix_mult air bir vm).
                 unfold VMatrix_MMatrix.
                 entailer!.
                 unfold IRMatrix_mult at 4 5.
                 unfold vupdate_dim at 1 2.
                 rewrite update_loop1_m, update_loop1_n, IRMatrix_mult_part1_m, IRMatrix_mult_part1_n.
                 cbn [vmatrix_m vmatrix_n].
                 rewrite Forall_is_float; [entailer!|].
                 specialize (vmax_data (IRMatrix_mult air bir (VMatrix_init_part1 VMatrix_default MAX_N))) as P2.
                 rewrite andb_true_iff, Nat.eqb_eq, forallb_forall in P2.
                 setoid_rewrite Nat.eqb_eq in P2; destruct P2 as (P2 & P3).
                 unfold IRMatrix_mult in *.
                 rewrite Forall_nth; intros.
                 rewrite Forall_nth; intros.
                 rewrite P3 in H.
                 rewrite P2 in H1; [|apply nth_In; lia].
                 apply IRMatrix_mult1_is_float_full; [apply H|apply H1 | intros].
                 replace (vmatrix_data (VMatrix_init_part1 VMatrix_default 20)) with
                   (repeat (repeat (Vfloat f0) MAX_N) MAX_N).
                 --- rewrite ?nth_repeat'; unfold is_float; auto; lia.
                 --- vm_compute; auto.
Qed.
