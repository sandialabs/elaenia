open List

open Util
open Tree
open Interval
open Segment
open Stepfunction
open Memory
open Printing

exception UnassignedVariableException of string ;;
exception InvalidAccessException of string ;;

(* Abstraction *)
(* --------------------------------------------------- *)

let abst_flt (f : float) : segment = 
    { int = Intr { u = f ; l = f }; err = ulp f } ;;

let rec abst_typ (typ : ctyp) : atyp =
    match typ with
    | IntTyp   -> IntrTyp
    | FloatTyp -> AStepTyp 
    | ArrTyp t -> AArrTyp (abst_typ t) ;;

let rec abst_val (v : cval) : aval =
    match v with
    | CInt i     -> AInt (Intr { l = i ; u = i })
    | CFloat f   -> AFloat (StepF [abst_flt f]) 
    | CArr (a,l) -> 
        let new_tbl = arr_bot () in
        List.iter (fun i -> Hashtbl.replace new_tbl i (abst_val (a i))) 
                  (int_seq l) ;
        AArr (new_tbl, l) ;;

let rec abst_aexp (exp : caexp) : aaexp = 
    match exp with
    | CVal v         -> AVal (abst_val v)
    | CVar (n, t)    -> AVar (n, abst_typ t)
    | CAcc (n, i, t) -> AAcc (n, Option.map abst_aexp i, abst_typ t)
    | CAdd (l, r)    -> AAdd ((abst_aexp l), (abst_aexp r))
    | CSub (l, r)    -> ASub ((abst_aexp l), (abst_aexp r))
    | CMul (l, r)    -> AMul ((abst_aexp l), (abst_aexp r))
    | CDiv (l, r)    -> ADiv ((abst_aexp l), (abst_aexp r)) ;;

let abst_bexp (exp : cbexp) : abexp =
    match exp with
    | CLt (l, r) -> ALt ((abst_aexp l), (abst_aexp r))
    | CLe (l, r) -> ALe ((abst_aexp l), (abst_aexp r))
    | CEq (l, r) -> AEq ((abst_aexp l), (abst_aexp r))
    | CNe (l, r) -> ANe ((abst_aexp l), (abst_aexp r))
    | CGe (l, r) -> AGe ((abst_aexp l), (abst_aexp r))
    | CGt (l, r) -> AGt ((abst_aexp l), (abst_aexp r)) ;;
    
let rec abst_stmt (exp : cstmt) : astmt = 
    match exp with
    | CAsgn ((n, i), v) -> 
        AAsgn ((n, Option.map abst_aexp i), (abst_aexp v))
    | CIf (b, t, e) -> 
        AIf ((abst_bexp b), (abst_stmt t), (abst_stmt e))
    | CFor (i, c, b, a) -> 
        AFor ((abst_stmt i), (abst_bexp c), (abst_stmt b), (abst_stmt a))
    | CCol (f, s) -> 
        ACol ((abst_stmt f), (abst_stmt s)) 
    | CRet aexp ->
        ARet (abst_aexp aexp) 
    ;;

(* Abstract semantics *)
(* --------------------------------------------------- *)
let aval_op (l : aval) (r : aval) 
            (iintr_op : int intr -> int intr -> int intr) 
            (sf_op : stepF -> stepF -> stepF) 
            : aval = 
    match l, r with
    | AInt ii1, AInt ii2 -> AInt (iintr_op ii1 ii2)
    | AInt ii, AFloat et | AFloat et, AInt ii -> 
        AInt (iintr_op ii (sf_to_iintr et))
    | AFloat et1, AFloat et2 -> AFloat (sf_op et1 et2)
    | AArr _, _ | _, AArr _ -> failwith "cannot do arithmetic on arrays"
    | ABot, _ | _, ABot -> ABot
    ;;

(* Arithmetic Expressions *)
(* --------------------------------------------------- *)
let rec asem_aexp (intervals : int) (exp : aaexp) (mem : amem) : (aval * id) =
    let asem_aexp_ints = asem_aexp intervals in
    match exp with
    | AVal e      -> 
        (e, Const)
    | AVar (n, _) -> (
        match lookup mem n with
        | Some v -> (v, Id n)
        | None -> raise (UnassignedVariableException n))
    | AAcc (n, i, _) -> (
        let index = Option.map (fun x -> fst @@ asem_aexp_ints x mem) i in
        match lookup mem n with
        | Some (AArr (a,_)) -> 
            (index_array a index intervals, ArrElem (n, extract_index i mem intervals))
        | Some v -> raise (InvalidAccessException 
                           ("Attempting to access non-array (" ^ n ^ 
                            ") with non-integer: " ^
                            Printing.str_aval v))
        | None -> raise (UnassignedVariableException n))
    | AAdd (l, r) -> 
        (aval_op (fst (asem_aexp_ints l mem)) 
                 (fst (asem_aexp_ints r mem)) 
                 iintr_add (eadd intervals), Const)
    | ASub (l, r) -> 
        (aval_op (fst (asem_aexp_ints l mem)) 
                 (fst (asem_aexp_ints r mem)) 
                 iintr_sub (esub intervals), Const)
    | AMul (l, r) ->
        (aval_op (fst (asem_aexp_ints l mem)) 
                 (fst (asem_aexp_ints r mem))
                 iintr_mul (emul intervals), Const)
    | ADiv (l, r) -> 
        (aval_op (fst (asem_aexp_ints l mem)) 
                 (fst (asem_aexp_ints r mem)) 
                 iintr_div (ediv intervals), Const)

and index_array (a : arr) (inter : aval option) (intervals : int) : aval =
    match inter with
    | Some (AInt i) -> (
        (* Get the union of all possible values for the index *)
        match iintr_range i with
        | i :: is -> fold_left (fun acc j -> aval_union intervals acc (Hashtbl.find a j)) 
                               (Hashtbl.find a i) is
        | [] -> ABot)
    | _ -> raise (InvalidAccessException 
                  "Attempting to index an array with something other than an int") 

(* Get the index represented by an aval *)
and extract_index (a : aaexp option) (mem : amem) (intervals : int) : int intr =
    let index = Option.map (fun x -> fst @@ asem_aexp intervals x mem) a in
    match index with
    | Some av -> (
        match av with
        | AInt i -> i
        | _      -> failwith "Attempting to index an array with something other than an int")
    | None -> failwith "Attempting to access an array with no index" ;;

(* Abstract boolean operators *)
(* --------------------------------------------------- *)
let abst_op (left : stepF) (right : stepF) 
            (op : stepF -> stepF -> (stepF * stepF)) : (stepF * stepF) =
    match left, right with
    | StepF _, StepF _ -> 
        let (new_l, new_r) = op left right in
        (new_l, new_r)
    | _, _ -> (Bot, Bot) ;;
    

(* Need to maintain the types of each side of the operator *)
let abst_bool_op (iintr_op : int intr -> int intr -> (int intr * int intr))
                 (sf_op : stepF -> stepF -> (stepF * stepF))
                 (l : aval * id) (r : aval * id) 
                 : ((aval * id) * (aval * id)) = 

    let (ltrm, lid), (rtrm, rid) = l, r in

    (* wrap into a tuple *)
    let wrap_int (l, r : int intr * int intr) : (aval * id) * (aval * id) = 
        ((AInt l, lid), (AInt r, rid)) in

    let wrap_flt (l, r : stepF * stepF) : (aval * id) * (aval * id) =
        ((AFloat l, lid), (AFloat r, rid)) in

    match ltrm, rtrm with
    | AFloat sf1, AFloat sf2 -> wrap_flt (abst_op sf1 sf2 sf_op)
    | AInt ii1, AInt ii2 -> wrap_int (iintr_op ii1 ii2)
    | AInt ii, AFloat sf -> 
        ((AInt (fst (iintr_op ii (sf_to_iintr sf))), lid), 
         (AFloat (snd (sf_op (iintr_to_sf ii) sf)), rid))
    | AFloat sf, AInt ii -> 
        ((AFloat (fst (sf_op sf (iintr_to_sf ii))), lid),
         (AInt (snd (iintr_op (sf_to_iintr sf) ii)), rid))
    | AArr _, _ | _, AArr _ -> failwith "cannot compare arrays"
    | ABot , AFloat sf2 -> wrap_flt (abst_op Bot sf2 sf_op)
    | AFloat sf1 , ABot -> wrap_flt (abst_op sf1 Bot sf_op)
    | ABot, AInt ii2 -> wrap_int (iintr_op IntrBot ii2)
    | AInt ii1, ABot -> wrap_int (iintr_op ii1 IntrBot)
    | ABot, ABot ->  ((ABot, lid), (ABot, rid))
    ;;

let abst_lt = abst_bool_op iintr_lt sf_lt ;;
let abst_le = abst_bool_op iintr_le sf_le ;;
let abst_gt = abst_bool_op iintr_gt sf_gt ;;
let abst_ge = abst_bool_op iintr_ge sf_ge ;;
let abst_eq = abst_bool_op iintr_eq sf_eq ;;
let abst_neq = abst_bool_op iintr_neq sf_neq ;;

(* Abstract Semantics of boolean expressions *)
(* --------------------------------------------------- *)
let asem_bexp (intervals : int) (exp : abexp) (m : amem) : amem =
    let asem_aexp_int = asem_aexp intervals in
    let amem_update_int = amem_update intervals in
    match exp with
    | ALt (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = abst_lt (asem_aexp_int l m) (asem_aexp_int r m) in
        amem_update_int lid new_l (amem_update_int rid new_r m)
    | ALe (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = abst_le (asem_aexp_int l m) (asem_aexp_int r m) in
        amem_update_int lid new_l (amem_update_int rid new_r m)
    | AEq (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = abst_eq (asem_aexp_int l m) (asem_aexp_int r m) in
        amem_update_int lid new_l (amem_update_int rid new_r m)
    | ANe _ -> m
    | AGe (l, r) ->
        let ((new_l, lid), (new_r, rid)) = abst_ge (asem_aexp_int l m) (asem_aexp_int r m) in
        amem_update_int lid new_l (amem_update_int rid new_r m)
    | AGt (l, r) -> 
        let ((new_l, lid), (new_r, rid)) = abst_gt (asem_aexp_int l m) (asem_aexp_int r m) in
        amem_update_int lid new_l (amem_update_int rid new_r m)

(* u_mem : amem -> amem -> amem *)
let u_amem mem1 mem2 (intervals : int) = 
    let { dom = dom1 ; tbl = m1 } = mem1 in
    let { dom = dom2 ; tbl = m2 } = mem2 in
    let dom3 = SS.union dom1 dom2 in
    let new_tbl= Hashtbl.copy m1 in
    iter (fun x -> Hashtbl.replace new_tbl 
                                   x 
                                   (aval_union intervals
                                               (fail_lookup x m1)
                                               (fail_lookup x m2)))
         (SS.elements dom3) ;
    { dom = dom3 ;
      tbl = new_tbl } ;;


(* Widening and Narrowing 
 * Note that the order of the arguments matters.
 * ------------------------- *)

(* Step Functions 
 * widen the ends and widen each segment *)
let rec widen_sf (intervals : int) (sf1 : stepF) (sf2 : stepF) : stepF = 
    let sf_union_int = sf_union intervals in
    match sf1, sf2 with
    | StepF _, StepF _ ->
        (sf_union_int
            (sf_union_int
                (if (lower (range sf2) <= lower (range sf1)) 
                 then StepF [seg_of neg_infinity (lower (range sf1)) infinity]
                 else Bot)
                (if (upper (range sf2) >= upper (range sf1))
                 then StepF [seg_of (upper (range sf1)) infinity infinity]
                 else Bot))
            (StepF (widen_segs sf1 sf2)))
    | StepF _, Bot -> sf1
    | Bot, StepF _ -> sf2
    | Bot, Bot -> Bot

and widen_segs (sf1 : stepF) (sf2 : stepF) : segment list =
        map (fun s1 -> fold_left widen_seg s1 (get_segs sf2)) (get_segs sf1)

and widen_seg (s1 : segment) (s2 : segment) : segment =
    if seg_overlap s1 s2 && s1.err < s2.err
    then seg_of_intr s1.int infinity
    else s1 ;;

let rec narrow_sf (intervals : int) (sf1 : stepF) (sf2 : stepF) : stepF =
    let sf_union_int = sf_union intervals in
    match sf1, sf2 with
    | StepF _, StepF _ ->
        (sf_union_int
            (sf_union_int
                (if (lower (range sf1) = neg_infinity)
                 then StepF [low_seg sf2] 
                 else Bot)
                (if (upper (range sf1) = infinity)
                 then StepF [high_seg sf2]
                 else Bot))
            (StepF (narrow_segs sf1 sf2)))
    | StepF _, Bot -> sf1
    | Bot, StepF _ -> sf2
    | Bot, Bot -> Bot

and narrow_segs (sf1 : stepF) (sf2 : stepF) : segment list =
    let non_inf = fun s1 -> lower s1.int != neg_infinity &&
                            upper s1.int != infinity && 
                            s1.err = infinity in
    let candidates = (filter non_inf (get_segs sf1)) in
    map (fun s1 -> fold_left narrow_seg s1 (get_segs sf2)) candidates

and narrow_seg (s1 : segment) (s2 : segment) : segment =
    if seg_overlap s1 s2
    then seg_of_intr s1.int s2.err
    else s1 ;;

let widen_iintr (i1 : int intr) (i2 : int intr) : int intr =
    match i1, i2 with
    | Intr ii1, Intr ii2 ->
        let low = if ii1.l > ii2.l then min_int else ii1.l in
        let high = if ii1.u < ii2.u then max_int else ii1.u in
        iintr_of low high 
    | IntrBot, Intr _ -> iintr_of min_int max_int 
    | Intr _, IntrBot -> i1 
    | IntrBot, IntrBot -> IntrBot ;;

let narrow_iintr (i1 : int intr) (i2 : int intr) : int intr =
    let low = if lower i1 = min_int then lower i2 else lower i1 in
    let high = if upper i1 = max_int then upper i2 else upper i1 in
    iintr_of low high ;;

let rec itr_op_aval (sf_op : stepF -> stepF -> stepF) 
                    (iintr_op : int intr -> int intr -> int intr) 
                    (av1 : aval) (av2 : aval) : aval =
    match av1, av2 with
    | AFloat sf1, AFloat sf2 -> AFloat (sf_op sf1 sf2)
    | AFloat sf1, AInt i2 -> AInt (iintr_op (sf_to_iintr sf1) i2)
    | AInt i1, AFloat sf2 -> AInt (iintr_op i1 (sf_to_iintr sf2))
    | AInt i1, AInt i2 -> AInt (iintr_op i1 i2) 
    | AArr (a1, l1), AArr (a2, l2) -> apply (itr_op_aval sf_op iintr_op) a1 l1 a2 l2 
    | AArr _, _ | _, AArr _ -> failwith "Variable type changed between iterations"
    | ABot, _ -> av2
    | _, ABot -> av1;;


let widen_aval (intervals : int) (a1 : aval) (a2 : aval) : aval =
    itr_op_aval (widen_sf intervals) widen_iintr a1 a2 ;;

let narrow_aval (intervals : int) (a1 : aval) (a2 : aval) : aval =
    itr_op_aval (narrow_sf intervals) narrow_iintr a1 a2 ;;

let aval_opt_op (a1 : aval option) (a2 : aval option) 
                (op : aval -> aval -> aval) : aval  =
    match a1, a2 with
    | Some av1, Some av2 -> op av1 av2
    | _, _ -> failwith "Variable disappeared between iterations";;

let widen_aval_opt (intervals : int) (a1 : aval option) (a2 : aval option) : aval =
    aval_opt_op a1 a2 (widen_aval intervals) ;;

let narrow_aval_opt (intervals : int) (a1 : aval option) (a2 : aval option) : aval =
    aval_opt_op a1 a2 (narrow_aval intervals) ;;

let amem_op (mem1 : amem) (mem2 : amem) 
            (op : aval option -> aval option -> aval) 
            (intervals : int) : amem =
    fold_left (fun acc x -> amem_update intervals (Id x)
                                        (op (lookup acc x) 
                                            (lookup mem2 x)) 
                                        acc)
              mem1 (SS.elements mem2.dom) ;;

let widen_amem (intervals : int) (mem1 : amem) (mem2 : amem) : amem =
    amem_op mem1 mem2 (widen_aval_opt intervals) intervals ;;

let narrow_amem (intervals : int) (mem1 : amem) (mem2 : amem) : amem =
    amem_op mem1 mem2 (narrow_aval_opt intervals) intervals ;;

(* Bounded iteration with widening after n iterations *)
let rec abst_iter (intervals : int) (f : amem -> amem) (m : amem) (n : int) : amem =
    (*(abst_iter_down f (abst_iter_up f m n))*)
    (abst_iter_up intervals f m n)

(* upward iteration *)
and abst_iter_up (intervals : int) (f : amem -> amem) (m : amem) (n : int) : amem =
    (* if n = 0 then abst_iter_up_w f m else  *)
    if n = 0 then m else
    let next = f m in
    let unioned = u_amem m next intervals in
    if amem_eq unioned m 
    then unioned
    else abst_iter_up intervals f unioned (n - 1)

(* with widening *)
and abst_iter_up_w (intervals : int) (f : amem -> amem) (m : amem) : amem =
    let next = f m in
    let widened = widen_amem intervals m next in
    if amem_eq widened m 
    then widened
    else abst_iter_up_w intervals f widened

and abst_iter_down (intervals : int) (f : amem -> amem) (m : amem) : amem =
    let next = f m in
    let narrowed = narrow_amem intervals m next in
    if amem_eq narrowed m
    then narrowed
    else abst_iter_down intervals f narrowed;;

let comp f g x = f (g x) ;;

(* 
 * An explicit return variable is placed in memory for outputting to ACSL.  If
 * the return value is a variable then the old variable identifier is removed from memory 
 *)
let rec asem_stmt (intervals : int) (exp : astmt) (iters : int) (m : amem) : amem =
    let asem_stmt_int = asem_stmt intervals in
    let asem_bexp_int = asem_bexp intervals in
    match exp with
    | AAsgn ((id, idx), e) -> 
        let ident = if Option.is_some idx 
                    then ArrElem (id, extract_index idx m intervals)
                    else Id id in
        amem_update intervals ident (fst (asem_aexp intervals e m)) m 
    | AIf (c, t, e) -> 
        u_amem
            (u_amem (asem_stmt_int t iters (asem_bexp_int c m)) 
                    (asem_stmt_int e iters (asem_bexp_int (not_abexp c) m)) intervals)
            (unstable_branch c t e iters m intervals)
            intervals
    | AFor (f, c, a, b) -> 
        let body = comp (asem_stmt_int a iters) 
                        (comp (asem_stmt_int b iters) (asem_bexp_int c)) in
        asem_bexp_int (not_abexp c) (abst_iter intervals body (asem_stmt_int f iters m) iters)
    | ACol (s1, s2) -> asem_stmt_int s2 iters (asem_stmt_int s1 iters m) 
    | ARet ex -> 
        (let (ret, n) = asem_aexp intervals ex m in
         match n with
         | Id n -> amem_rename intervals (Id n) "result" m
         | _    -> amem_update intervals (Id "result") ret m)


(* Branch Instability *)
(* ---------------------------- *)

(* Find the unstable region of a condition *)
(* A little bit of a hack since abst_eq computes the overlap *)
and filter_unstable (intervals : int) (exp : abexp) (m : amem) : amem =
    let asem_aexp_int = asem_aexp intervals in
    let amem_update_int = amem_update intervals in
    match exp with
    | ALt (l, r) | ALe (l, r) | AEq (l, r) | ANe (l, r) | AGe (l, r) | AGt (l, r) ->
        let ((new_l, lid), (new_r, rid)) = abst_eq (asem_aexp_int l m) (asem_aexp_int r m) in
        amem_update_int lid new_l (amem_update_int rid new_r m)

(* find the error between the branches 
   map each variable to a new interval based on the then branch and other things*)
and unstable_branch (exp : abexp) (t : astmt) (e : astmt) 
                    (i : int) (m : amem) (intervals : int) : amem =
    let asem_stmt_int = asem_stmt intervals in
    let amem_update_int = amem_update intervals in
    let fu = filter_unstable intervals exp m in
    let m1, m2 = asem_stmt_int t i fu, asem_stmt_int e i fu in
    u_amem 
        (* then branch *)
        (fold_left (fun a x -> amem_update_int (Id x) (unstable_aval x m1 m2) a) 
                   amem_bot (SS.elements m1.dom)) 
        (* else branch *)
        (fold_left (fun a x -> amem_update_int (Id x) (unstable_aval x m2 m1) a) 
                   amem_bot (SS.elements m2.dom))
        intervals

(* What is the difference between branch m1 and branch m2? Assuming we took
 * branch m1. *)
and unstable_aval (x: string) (m1 : amem) (m2 : amem) : aval =
    let x1, x2 = lookup m1 x, lookup m2 x in
    match x1, x2 with
    | Some av1, Some av2 -> both_branches av1 av2
    | Some av1, None -> one_branch av1
    | None, Some av2 -> one_branch av2
    | None, None -> raise (UnassignedVariableException "Neither branch assigned?")

(* If both branches have the value then either the error or the difference *)
and both_branches (av1 : aval) (av2 : aval) : aval =
    match av1, av2 with
    | AFloat (StepF sf1), AFloat (StepF sf2) ->
        AFloat (StepF 
            (map (fun seg -> seg_of_intr seg.int (max_flt [seg.err ; diff_intr seg.int (range (StepF sf2))])) sf1))
    | AFloat (StepF sf1), AFloat Bot ->
        AFloat (StepF
            (map (fun seg -> seg_of_intr seg.int infinity) sf1))
    | AFloat (StepF sf1), AInt i -> 
        AFloat (StepF
            (map (fun seg -> seg_of_intr seg.int (max_flt [seg.err ; diff_intr seg.int (iintr_to_intr i)])) sf1))
    | _, _ -> av1

(* if the other branch doesn't have a value then our error is infinite *)
and one_branch (a : aval) : aval =
    match a with
    | AFloat (StepF sf) -> 
        AFloat (StepF (map (fun s -> seg_of_intr s.int infinity) sf))
    | _         -> a ;;

let abst_interp exp m intervals = asem_stmt intervals exp 20 m ;;
