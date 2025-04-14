open List
open Util
open Interval
open Segment

(* Models a step function, the interval is the domain and the err is the value
   in that interval *)
type stepF = Bot | StepF of segment list ;;
let sf_of l u e = StepF [seg_of l u e] ;;

(* Utilities *)
(* ------------------------- *)

(* Get the range of the step function as an interval.  If the domain is
 * non-continuous this function treats it as continuous *)
let range (sf : stepF) : float intr = 
    match sf with
    | StepF segs -> Intr { l = min_flt (map (fun seg -> lower seg.int) segs) ;
                           u = max_flt (map (fun seg -> upper seg.int) segs) }
    | Bot        -> IntrBot ;;


(* Utility to get the range as a segment datatype *)
let range_seg (sf : stepF) : segment = 
    let intr = range sf in
    seg_of_intr intr 0.0 ;;

let get_segs (sf : stepF) : segment list = 
    match sf with
    | StepF segs -> segs
    | Bot -> [] ;;

let sf_append (sf : stepF) (segs : segment list) = 
    match sf with
    | StepF errs -> StepF (segs @ errs)
    | Bot -> 
        (match segs with
         | [] -> Bot
         | _  -> StepF segs) ;;

(* Get the range and the upperbound of the error as a segment datatype *)
let rec single_seg (sf : stepF) : segment =
    let intr = range sf in
    seg_of_intr intr (err_upper_bound sf)

and err_upper_bound (sf : stepF) : float =
    fold_left (fun acc s -> if s.err > acc then s.err else acc) 0.0 (get_segs sf) ;;


(* Convert to and from an integer interval for casting purposes *)
let sf_to_iintr (sf : stepF) : int intr = intr_to_iintr (range sf) ;;
let iintr_to_sf (ii : int intr) = 
    match ii with
    | Intr i -> StepF [seg_of (Float.of_int i.l) (Float.of_int i.u) 0.0]
    | _ -> Bot ;;

(* Get the segment with the smallest lower bound *)
let low_seg (sf : stepF) : segment = 
    match sf with
    | StepF segs ->
        fold_left (fun s acc -> if lower s.int < lower acc.int then s else acc) 
                  (seg_of infinity infinity infinity)
                  segs
    | _ -> failwith "attempting to get lower segment of an error value";;

(* Get the segment with the largest upper bound *)
let high_seg (sf : stepF) : segment = 
    match sf with
    | StepF segs ->
        fold_left (fun s acc -> if upper s.int > lower acc.int then s else acc) 
                  (seg_of neg_infinity neg_infinity infinity)
                  segs
    | _ -> failwith "attempting to get upper segment of an error value";;


(* Merging *)
(* ------------------------- *)
let combine_seg (s1 : segment) (s2 : segment) : segment =
    seg_of (min_flt [lower s1.int ; lower s2.int]) 
           (max_flt [upper s1.int ; upper s2.int]) s1.err
;;

let merge_seg (s1 : segment) (s2 : segment) : segment =
    seg_of (min_flt [lower s1.int ; lower s2.int]) 
           (max_flt [upper s1.int ; upper s2.int]) 
           (max_flt [s1.err ; s2.err])
;;


(* The three cases discussed below.  The constructor holds the segment to be merged *)
type adjacency = Peak | Trough of segment | Stair of segment

(* Limit the stepfunction to maximum number of intervals.  The smallest
 * intervals (by range covered) are merged into their adjacent intervals. 
 *
 * There are 3 cases to distinguish:
 * 1. The interval is between a higher and lower error bound.
 * 2. The interval is between two higher error bounds.
 * 3. The interval is between two lower error bounds.
 * 
 * The algorithm will attempt to not merge any intervals in case 3 as that
 * could add significant imprecision to the analysis.  For the first case the
 * segment will get merged with adjacent segment with a higher bound to ensure 
 * the approximation is still sound.  For the second case the segment will get
 * merged with the segement with a lower bound.  This maintains soundness as we
 * are raising the error approximation while being as precise as possible.
 *
 *)
let rec limit (sf : stepF) (intervals : int) : stepF =
    let num_segs = length (get_segs sf) in
    if num_segs <= intervals 
    then sf
    else 
        let small_first = sort_by_size (get_segs sf) in
        StepF (limit_inner small_first (num_segs - intervals) [])

(* 
 * segs : The segments of the step function
 * intervals : The number of intervals to merge
 * acc : An accumulator stores peaks that were skipped 
 *)
and limit_inner (segs : segment list) (intervals : int) 
                (acc : segment list) : segment list =
    if intervals <= 0 
    then append acc segs
    else
        match segs with
        | []      -> 
            limit_inner (sort_by_size (append acc segs)) intervals []
        | x :: xs -> 
            (match limit_merge x segs acc with
             | None -> 
                limit_inner xs intervals (x :: acc)
             | Some (new_seg, new_list, new_acc) ->
                limit_inner new_list (intervals - 1) new_acc)

and sort_by_size (segs : segment list) : segment list =
    sort (fun s1 s2 -> Float.compare (intr_size s1.int) (intr_size s2.int)) segs

(* Merges seg into segs.  Returns a new list of segments containing the
 * combined segment and neither of the merged segments.  Also returns the 
 * accumulator with removed segments. If seg is a peak it does nothing.
 *)
and limit_merge (seg : segment) (segs : segment list) 
                (peaks : segment list) : (segment * segment list * segment list) option =
    match determine_adjacency seg (get_adjacent_segments seg (append segs peaks)) with
    | Peak -> None
    | Trough s | Stair s -> 
        let new_seg = merge_seg seg s in
        Some (new_seg, 
              sort_by_size (new_seg :: filter (fun s' -> (not (s' = s)) && (not (s' = seg))) segs),
              (filter (fun s' -> (not (s' = s))) peaks))

and get_adjacent_segments (seg : segment) (segs : segment list) : segment list =
    filter (fun s -> seg_adjacent s seg) segs

and determine_adjacency (seg : segment) (segs : segment list) : adjacency =
    fold_left (fun acc s -> update_adjacency acc seg s) Peak segs

and update_adjacency (adj : adjacency) (seg : segment) (adj_seg : segment) : adjacency = 
    if adj_seg.err <= seg.err 
    then adj
    else 
        match adj with
        | Peak     -> Stair adj_seg
        | Stair s  -> Trough (if s.err > adj_seg.err then adj_seg else s)
        | Trough _ -> raise (IntervalError "limit failed at determining adjacent segments.")

;;


let cnt = ref 0;;
let tot = ref 0;;

(* Merge with adjacency comparing.  Combines adjacent intervals with the same
   error.*)
let rec merge (sf : stepF) (intervals : int) : stepF =
    let err_first = 
        sort (fun s1 s2 -> Float.compare s2.err s1.err) (get_segs sf) in
    tot := length err_first ;
    cnt := 0 ;
    StepF (merge_inner [] [] err_first false)

(* 
 * Parameters:
 *   dom : The domain of the accumulator
 *   acc : Accumulator for the new step function
 *   lst : The unmerged segments of the old step function
 *   has_nan : Is there a NaN segment in the step function?
 *)
and merge_inner (dom : float intr list) (acc : segment list) 
                (lst : segment list) (has_nan : bool) : segment list = 
    cnt := !cnt + 1;
    match lst with
    | x :: xs -> 
        (* If there is a NaN segment then we stop merging *)
        if has_nan && not (is_valid x.int) 
        then acc
        (* If the two segments are adjacent and have the same error we combine them *)
        else (if length acc > 0 &&
                x.err = (hd acc).err && 
                (intr_adjacent x.int (hd acc).int || intr_overlap x.int (hd acc).int)
        then
            merge_inner (expand_domain dom x.int)
                        (combine_seg x (hd acc) :: tl acc)
                        xs
                        (has_nan || (not (is_valid x.int)))
        (* Otherwise we add to the accumulator *)
        else
            merge_inner (expand_domain dom x.int) 
                        ((seg_withouts_intr x dom) @ acc)
                        xs
                        (has_nan || (not (is_valid x.int))))
    | [] -> acc
and expand_domain (dom : float intr list) (i : float intr) : float intr list =
    match dom with
    | x :: xs ->
        if intr_overlap i x || intr_adjacent i x
        then expand_domain xs (intr_union x i)
        else x :: expand_domain xs i
    | [] -> [i] ;;


(* Arithmetic operators *)
(* ------------------------- *)

(* generic step-function operation *)
let rec eop (l : stepF) (r : stepF) 
            (op : segment -> segment -> segment list) 
            (prop_err_op : segment -> segment -> float)
            (intervals : int)
            : stepF =
    match l, r with
    | StepF ls, StepF rs ->
        let is = concat 
            (product_map (fun x y -> 
                            let perr = prop_err_op x y in
                            (map (fun s -> {s with err = perr}) 
                                          (op x y))) 
                         ls rs) in
        let ms = merge (StepF is) intervals in
        let ret = concat (map (fun s -> binade_split_seg s) 
                         (get_segs ms)) in 
        limit (merge (StepF ret) intervals) intervals ;
    | _, _ -> Bot

(* Binade splitting on segments *)
and binade_split_seg (s : segment) : segment list =
    let is = split_binade s.int in
    map (fun i -> { int = i ; err = s.err +. ulp_intr i }) is ;;

let eadd (intervals : int) (l : stepF) (r : stepF) : stepF = 
    eop l r seg_add err_add_prop intervals ;;

let esub (intervals : int) (l : stepF) (r : stepF) : stepF = 
    eop l r seg_sub err_sub_prop intervals ;;

let emul (intervals : int) (l : stepF) (r : stepF) : stepF = 
    eop l r seg_mul err_mul_prop intervals ;;

let ediv (intervals : int) (l : stepF) (r : stepF) : stepF = 
    eop l r seg_div err_div_prop intervals ;;


(* Boolean operators *)
(* Get overlapping portion of both step-functions *)
let overlap (s1: stepF) (s2: stepF) : (stepF * stepF) =
    match s1, s2 with
    | StepF segs1, StepF segs2 ->
        let ov = intr_with (range s1) (range s2) in
        (StepF (filter_map (fun s -> seg_with_intr s ov) segs1),
         StepF (filter_map (fun s -> seg_with_intr s ov) segs2))
    | Bot, _ | _, Bot -> (Bot, Bot) ;;

(* Chops based upen segment comparison function passed in *)
let chop (sf : stepF) (range : float intr) 
         (comp : segment -> segment -> (segment * segment)) : stepF =
    match range with
    | Intr _ ->
        (match sf with
         | StepF segs ->
               let dummy = seg_of_intr range 0.0 in
               StepF (filter (fun x -> x != seg_bot) 
                             (map (fun x -> fst (comp x dummy)) segs))
         | Bot -> Bot ) 
    | _ -> Bot ;;

let sf_lt l r = (chop l (range r) seg_lt, chop r (range l) seg_gt) ;;
let sf_le l r = (chop l (range r) seg_le, chop r (range l) seg_ge) ;;
let sf_gt l r = (chop l (range r) seg_gt, chop r (range l) seg_lt) ;;
let sf_ge l r = (chop l (range r) seg_ge, chop r (range l) seg_le) ;;
let sf_eq l r = (chop l (range r) seg_eq, chop r (range l) seg_eq) ;; 
let sf_neq l r = (l, r) ;;

(* Union *)
let sf_union (intervals : int) (l : stepF) (r : stepF) : stepF =
    merge (sf_append l (get_segs r)) intervals ;;
