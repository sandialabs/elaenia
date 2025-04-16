open List

open Interval

(* The interval-error terms.  Represents a section of the interval with an
   associated error *)
type segment = {
    int : float intr;
    err : float
} ;;

let seg_bot = { int = IntrBot ; err = 0. } ;;

(* Utilities *)
(* ------------------------------ *)
let seg_of l u err = 
    if l > u || err < 0.
    then seg_bot 
    else { int = intr_of l u ; err = err } ;;

let seg_of_intr i err =
    match i with
    | Intr _ -> { int = i ; err = err } 
    | IntrBot -> { int = i ; err = 0. } ;;

let seg_overlap s1 s2 = intr_overlap s1.int s2.int ;;

let lower_bnd (s : segment) : float = lower s.int ;;
let upper_bnd (s : segment) : float = upper s.int ;;

let seg_to_intr (s : segment) : float intr = s.int ;;

let seg_adjacent (seg1 : segment) (seg2 : segment) : bool =
    intr_adjacent seg1.int seg2.int

(* Same as intr without but maintain the error *)
(* Remove seg2 from seg1 *)
let seg_without (seg1 : segment) (seg2 : segment) : segment list =
    map (fun i -> seg_of_intr i seg1.err)
        (intr_without seg1.int seg2.int) ;;


let seg_withouts_intr (s1 : segment) (is : float intr list) : segment list =
    map (fun i -> seg_of_intr i s1.err) (intr_withouts s1.int is)

(* The portions of s1 that overlap with s2 
 * Note that the error of segment1 is maintained here *)
let seg_with (s1 : segment) (s2 : segment) : segment = 
    let overlap = intr_with s1.int s2.int in
    seg_of_intr overlap s1.err ;;

(* Same as above but works with intervals *)
let seg_with_intr (s : segment) (i : float intr) : segment option =
    let overlap = intr_with s.int i in
    match overlap with
    | Intr _ -> Some (seg_of_intr overlap s.err)
    | _ -> None ;;
    

(* First element of return is s1 without any overlap of s2.  Second element is
 * overlapping portion *)
let seg_partition (s1 : segment) (s2 : segment)
    : (segment list * segment) =
    (seg_without s1 s2, seg_with s1 s2) ;;

let ulp_op (l : segment) (r : segment) 
           (op : float interval -> float interval -> float) : float = 
    match l.int, r.int with
    | Intr li, Intr ri -> op li ri
    | IntrBot, _ | _, IntrBot -> 0. ;;

(* For these error functions, o is the result of the interval operation on l
 * and r.
 *
 * err_op_prop are the error propagation functions, for convenience.
 * ---------------------------------------------------------------------- *)
let err_add_prop (l : segment) (r : segment) : float = l.err +. r.err ;;
let err_add (l : segment) (r : segment) (o : float intr) : float = 
    (err_add_prop l r) +. (ulp_intr o) ;;

let err_sub_prop (l : segment) (r : segment) : float = l.err +. r.err ;;
let err_sub (l : segment) (r : segment) (o : float intr) : float = 
    (err_sub_prop l r) +. (ulp_intr o) ;;

let err_sbenz (l : segment) (r : segment) (_ : float intr) : float = 
    l.err +. r.err ;;

let err_mul_prop (l : segment) (r : segment) : float =
    let lup = mag_lg_intr l.int in
    let rup = mag_lg_intr r.int in
    lup *. r.err +. rup *. l.err +. l.err *. r.err ;;

let err_mul (l : segment) (r : segment) (o : float intr) : float =
    (err_mul_prop l r) +. (ulp_intr o) ;;

let err_div_prop (l : segment) (r : segment) : float =
    let lup = mag_lg_intr l.int in
    let rdn = mag_sm_intr r.int in
    ((lup *. r.err +. rdn *. l.err) /. (rdn *. rdn -. rdn *. r.err)) ;;
    
let err_div (l : segment) (r : segment) (o : float intr) : float =
    (err_div_prop l r) +. (ulp_intr o) ;;

(* Sterbenz Lemma *)
(* ---------------------- *)
(* Before subtraction, find sections that meet the condition *)
(* Find Sterbenz stuff *)
let get_sterbenz_seg (seg : segment) : segment =
    seg_of_intr (get_sterbenz_intr seg.int) seg.err ;;

(* Arithmetic operators *)
(* ---------------------- *)
let seg_op (intr_op : float intr -> float intr -> float intr)
           (err_op : segment -> segment -> float intr -> float) 
           (x : segment) (y : segment) 
           : segment  =
    let op_out = intr_op x.int y.int in
    { int = op_out ; err = err_op x y op_out } ;;
    
let seg_add (x : segment) (y : segment) : segment list =
    [seg_op intr_add err_add x y]

(* No special cases *)
let seg_sub_reg (x : segment) (y : segment) : segment list =
    [seg_op intr_sub err_sub x y] ;;

(* Sterbenz *)
let seg_sub_sbenz (x : segment) (y : segment) : segment list =
    [seg_op intr_sub err_sbenz x y] ;;

let seg_sub (x : segment) (y : segment) : segment list = 
    let reg, sbenz = (seg_partition y (get_sterbenz_seg x)) in
    if sbenz = seg_bot 
    then concat_map (seg_sub_reg x) reg  
    else seg_sub_sbenz x sbenz @ concat_map (seg_sub_reg x) reg 

let seg_mul (x : segment) (y : segment) : segment list = 
    [seg_op intr_mul err_mul x y] ;;


let seg_div (x : segment) (y : segment) : segment list = 
    [seg_op intr_div err_div x y] ;;
(*
    (* If a possible divide by 0, note it and move on *)
    if contains y.int 0.0
    (* We remove the section that will produce an infinite result *)
    then 
        let div = smallest_finite_divisor (mag_lg_intr x.int) in
        let nonzero = seg_withouts_intr y [intr_of (-.div) div] in
        Format.printf "div = %30.30f\n nonzero = %s\n\n" div (str_segs nonzero) ; Format.print_flush () ;
        let ret = seg_bot :: map (seg_op intr_div err_div x) nonzero in
        Format.printf "ret = %s\n\n" (str_segs ret); ret
    else [seg_op intr_div err_div x y] ;;
    *)

(* TODO: End up with a segment from [min_float ; max_float] but has infinite error? *)


(* Boolean operators *)
(* ---------------------- *)
(* Return the new values of the operands *)
let seg_lt l r = 
    let (li, ri) = intr_lt l.int r.int in
    (seg_of_intr li l.err, seg_of_intr ri r.err) ;;

let seg_le l r = 
    let (li, ri) = intr_le l.int r.int in
    (seg_of_intr li l.err, seg_of_intr ri r.err) ;;

let seg_gt l r = 
    let (li, ri) = intr_gt l.int r.int in
    (seg_of_intr li l.err, seg_of_intr ri r.err) ;;

let seg_ge l r = 
    let (li, ri) = intr_ge l.int r.int in
    (seg_of_intr li l.err, seg_of_intr ri r.err) ;;

let seg_eq l r =
    let (li, ri) = intr_eq l.int r.int in
    (seg_of_intr li l.err, seg_of_intr ri r.err) ;;

let seg_neq l r = (l, r) ;;

(* Union *)
(* This type signature is odd, should probably return an eterm but an import
 * dependency cycle is introduced.  The resulting list has a domain the same
 * size as the union of the two intervals.
 *)
(* seg_union : segment -> segment -> segment list *)
let seg_union (l : segment) (r : segment) : segment list = 
    let (large, small) = if l.err >= r.err then (l, r) else (r, l) in
    let intrs = seg_without small large in
    [large] @ intrs ;;

