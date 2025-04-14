open Float
open List

open Round
open Util

exception IntervalError of string ;;


(* Interval definitions *)
(* -------------------------- *)
type 'a interval = { l : 'a ; u : 'a } ;;

(* Float interval *)
type 'a intr = IntrBot | Intr of 'a interval ;;

(* inclusive *)
let intr_of (l : 'a) (u : 'a) : 'a intr =
    if l > u then IntrBot else Intr {l = l ; u = u} ;;

(* exclusive *)
let intr_of_exc (l : float) (u : float) : float intr = 
    if l >= u then IntrBot else Intr {l = l ; u = u} ;;

let intr_of_int (i : int) : float intr = 
    Intr {l = Float.of_int i; u = Float.of_int i} ;;

let iintr_of (l : int) (u : int) : int intr =
    if l >= u then IntrBot else Intr {l = l ; u = u} ;;

(* Int interval *)
let intr_to_iintr (intr : float intr) : int intr = 
    match intr with
    | Intr i -> Intr { l = Int.of_float i.l ; u = Int.of_float (i.u +. 0.5) }
    | IntrBot -> IntrBot ;;

let iintr_to_intr (intr : int intr) : float intr =
    match intr with
    | Intr i -> Intr { l = Float.of_int i.l ; u = Float.of_int i.u }
    | IntrBot -> IntrBot ;;


(* Useful utils *)
(* -------------------------- *)
let intr_size i =
    match i with
    | Intr i -> Float.abs (i.u -. i.l)
    | _ -> 0. ;;

let is_valid i =
    match i with
    | Intr _ -> true
    | _ -> false ;;

let contains (intr : 'a intr) (v : 'a) : bool = 
    match intr with
    | Intr i -> i.l <= v && i.u >= v 
    | _ -> false ;;

let interval_overlap (i1 : 'a interval) (i2 : 'a interval) : bool = 
    i1.l <= i2.l && i1.u >= i2.l ||
    i2.l <= i1.l && i2.u >= i1.l ||
    i1.u >= i2.u && i1.l <= i2.u ||
    i2.u >= i1.u && i2.l <= i1.u ;;

let intr_overlap (intr1 : 'a intr) (intr2 : 'a intr) : bool = 
    match intr1, intr2 with
    | Intr i1, Intr i2 -> interval_overlap i1 i2 
    | IntrBot, _ | _, IntrBot -> false ;;


let intr_adjacent (intr1 : float intr) (intr2 : float intr) : bool =
    match intr1, intr2 with
    | Intr i1, Intr i2 ->
        i1.l = i2.u +. ulp(i2.u) ||
        i1.u = i2.l -. ulp(i2.l)
    | IntrBot, _ | _, IntrBot -> false ;;

let lower (intr : 'a intr) = 
    match intr with
    | Intr i -> i.l
    | _ -> failwith "No lower bound for error interval" ;;

let upper (intr : 'a intr) = 
    match intr with
    | Intr i -> i.u
    | _ -> failwith "No upper bound for error interval" ;;

let intr_to_interval intr = 
    match intr with
    | Intr i -> i
    | _ -> failwith "Attempting to extract interval from error intr" ;; 

(* Largest and smallest constraint by magnitude *)
let mag_lg (i: float interval) : float = max_flt [(abs i.l) ; (abs i.u)] ;;
let mag_lg_intr (intr : float intr) : float =
    match intr with
    | Intr i -> mag_lg i
    | IntrBot -> nan ;;

(* If we cross 0 then 0, else whichever one is closer to 0 *)
let mag_sm i = 
    if i.l < 0. && i.u > 0.
    then 0.
    else min_flt [(abs i.l) ; (abs i.u)] ;;

let mag_sm_intr (intr : float intr) : float =
    match intr with
    | Intr i -> mag_sm i
    | IntrBot -> nan ;;

let ulp_intr (i : float intr) = ulp (mag_lg_intr i) ;;

(* Get the largest difference of values between two intervals *)
let diff_interval (i1 : float interval) (i2 : float interval) : float =
    max_flt [abs (i1.u -. i2.l) ; abs (i2.u -. i1.l)] ;;


let diff_intr (i1 : float intr) (i2 : float intr) : float =
    let ret =
        match i1, i2 with
        | Intr in1, Intr in2 -> diff_interval in1 in2
        | _, _ -> nan 
    in if ret = infinity then 
            raise (IntervalError "infinity value in diff_intr")
        else ret;;

(* Get the floating point value of the upper bound of binade defined by
 * exponent exp *)
let exp_to_binade (exp : int) : float = pow 2. (Float.of_int exp) ;;

(* get the integers in an int interval *)
let iintr_range (x : int intr) : int list =
    match x with
    | Intr i -> List.init (i.u - i.l + 1) ((+) i.l)
    | _      -> [] ;;
    

(* Splitting Intervals *)
(* -------------------------- *)
(* Split an interval on each binade with the lower bound being 1 ulp above the
 * previous binade .
 * 
 * We avoid subnormal numbers by taking the minimum normal binade.
 *)
let split_binade_pos (i : float interval) : float intr list =
    let (_, el) = frexp (Float.max min_float i.l) in (* the smallest exponent *)
    let (_, eu) = frexp i.u in                       (* the largest exponent *)
    let init_intr = intr_of i.l (pred (exp_to_binade el)) in
    let final_intr = intr_of (exp_to_binade (eu - 1)) i.u in
    let middle_intrs = 
        List.init (Int.abs (eu - el - 1))
                  (fun x -> intr_of (exp_to_binade (x + el))
                                    (pred (exp_to_binade (x + 1 + el)))) in
    init_intr :: middle_intrs @ [final_intr] ;;


(* The lower bound will have a larger exponent *)
let split_binade_neg (i : float interval) : float intr list =
    let (_, el) = frexp i.l in                           (* the largest exponent *)
    let (_, eu) = frexp (Float.min (-.min_float) i.u) in (* the smallest exponent *)
    let init_intr = intr_of i.l (-.(exp_to_binade (el - 1))) in
    let final_intr = intr_of (succ (-.(exp_to_binade eu))) i.u in
    let middle_intrs = 
        List.init (Int.abs (el - eu - 1))
                  (fun x -> intr_of (succ (-.(exp_to_binade (el - x - 1))))
                                    (-.(exp_to_binade (el - x - 2)))) in
    init_intr :: middle_intrs @ [final_intr] ;;


let split_binade (intr : float intr) : float intr list =
    let pos_lb, neg_ub = (succ 0. , pred 0.)in
    match intr with
    | Intr i -> 
        if snd (frexp i.l) = snd (frexp i.u) &&
           (i.l > 0. || i.u < 0.) then [intr] else 
        if i.l = 0. then 
            intr_of 0. pos_lb  :: 
            split_binade_pos {l = pos_lb ; u = i.u} else
        if i.u = 0. then 
            intr_of neg_ub 0. :: 
            split_binade_neg {l = i.l ; u = neg_ub} else
        if i.l > 0. then split_binade_pos i else 
        if i.u < 0. then split_binade_neg i else (
            split_binade_neg { l = i.l ; u = neg_ub } @
            [ intr_of 0. 0. ] @
            split_binade_pos { l = pos_lb ; u = i.u })
    | _ -> ([intr]) ;;


(* Arithmetic operators *)
(* -------------------------- *)
(* Ints *)

let iintr_add_op l r = Intr { l = l.l + r.l ; u = l.u + r.u } ;;
let iintr_sub_op l r = Intr { l = l.l - r.u ; u = l.u + r.l } ;;
let iintr_mul_op l r = 
    let combos = [l.l * r.l ; l.l * r.u ; l.u * r.l ; l.u * r.u] in 
    Intr { l = min_ints combos ; u = max_ints combos }
let iintr_div_op l r = 
    if r.l < 0 && r.u > 0 
    then Intr { l = min_int ; u = max_int }
    else let combos = [l.l / r.l ; l.l / r.u ; l.u / r.l ; l.u / r.u] in 
         Intr { l = min_ints combos ; u = max_ints combos } ;;


(* Floats *)
(* Down / Up are the rounding modes *)
let intr_add_op l r = Intr { l = add Down l.l r.l ; u = add Up l.u r.u } ;;
let intr_sub_op l r = Intr { l = sub Down l.l r.u ; u = sub Up l.u r.l } ;;
let intr_mul_op l r = 
    let combos = [mul Down l.l r.l ; mul Down l.l r.u ;
                  mul Down l.u r.l ; mul Down l.u r.u] in
    Intr { l = min_flt combos ; u = max_flt combos } ;;
let intr_div_op l r = 
    if r.l < 0. && r.u > 0.
    then Intr { l = neg_infinity ; u = infinity }
    else let combos = [div Down l.l r.l ; div Down l.l r.u ;
                  div Down l.u r.l ; div Down l.u r.u] in
         Intr { l = min_flt combos ; u = max_flt combos } ;;


let intr_op (left : 'a intr) (right : 'a intr) 
             (op : 'a interval -> 'a interval -> 'a intr) = 
    match left, right with
    | Intr l, Intr r  -> op l r
    | IntrBot, _ | _, IntrBot -> IntrBot

let iintr_add l r = intr_op l r iintr_add_op ;;
let iintr_sub l r = intr_op l r iintr_sub_op ;;
let iintr_mul l r = intr_op l r iintr_mul_op ;;
let iintr_div l r = intr_op l r iintr_div_op ;;

let intr_add l r = intr_op l r intr_add_op ;; 
let intr_sub l r = intr_op l r intr_sub_op ;; 
let intr_mul l r = intr_op l r intr_mul_op ;; 
let intr_div l r = intr_op l r intr_div_op ;; 


(* Boolean Operators *)
(* -------------------------- *)
(* Returns the new values of the operands *)
(* Ints *)
let iintr_lt_op l r = 
    let lu = min_ints [l.u ; r.u - 1] in
    let rl = max_ints [l.l + 1 ; r.l] in
    (intr_of l.l lu, intr_of rl r.u) ;;

let iintr_le_op l r = 
    let lu = min_ints [l.u ; r.u] in
    let rl = max_ints [l.l ; r.l] in
    (intr_of l.l lu, intr_of rl r.u) ;;

let iintr_gt_op l r = 
    let ll = max_ints [l.l ; r.l + 1] in
    let ru = min_ints [r.u ; l.u - 1] in
    (intr_of ll l.u, intr_of r.l ru) ;;

let iintr_ge_op l r = 
    let ll = max_ints [l.l ; r.l] in
    let ru = min_ints [r.u ; l.u] in
    (intr_of ll l.u, intr_of r.l ru) ;;

let iintr_eq_op l r = 
    let new_iintr = intr_of (max_ints [l.l ; r.l]) (min_ints [l.u ; r.u]) in
    (new_iintr, new_iintr) ;;

(* Floats*)
let intr_lt_op l r = 
    let lu = min_flt [l.u ; r.u -. ulp r.u] in
    let rl = max_flt [l.l +. ulp l.l ; r.l] in
    (intr_of l.l lu, intr_of rl r.u) ;;

let intr_le_op l r =
    let lu = min_flt [l.u ; r.u] in
    let rl = max_flt [l.l ; r.l] in
    (intr_of l.l lu, intr_of rl r.u) ;;

let intr_gt_op l r = 
    let ll = max_flt [l.l ; r.l +. ulp r.l] in
    let ru = min_flt [r.u ; l.u -. ulp l.u] in
    (intr_of ll l.u, intr_of r.l ru) ;;

let intr_ge_op l r = 
    let ll = max_flt [l.l ; r.l] in
    let ru = min_flt [l.u ; r.u] in
    (intr_of ll l.u, intr_of r.l ru) ;;

let intr_eq_op l r = 
    let new_intr = intr_of (max_flt [l.l ; r.l]) (min_flt [l.u ; r.u]) in
    (new_intr, new_intr) ;;


let intr_bool_op (left : 'a intr) (right : 'a intr) 
                 (op : 'a interval -> 'a interval -> ('a intr * 'a intr)) 
                 : ('a intr * 'a intr) = 
    match left, right with
    | Intr l, Intr r -> op l r
    | IntrBot, _ | _, IntrBot -> (IntrBot, IntrBot) ;;

let iintr_lt l r = intr_bool_op l r iintr_lt_op ;;
let iintr_le l r = intr_bool_op l r iintr_le_op ;;
let iintr_gt l r = intr_bool_op l r iintr_gt_op ;;
let iintr_ge l r = intr_bool_op l r iintr_ge_op ;;
let iintr_eq l r = intr_bool_op l r iintr_eq_op ;;
let iintr_neq l r = (l, r)

let intr_lt l r = intr_bool_op l r intr_lt_op ;;
let intr_le l r = intr_bool_op l r intr_le_op ;;
let intr_gt l r = intr_bool_op l r intr_gt_op ;;
let intr_ge l r = intr_bool_op l r intr_ge_op ;;
let intr_eq l r = intr_bool_op l r intr_eq_op ;;
let intr_neq l r = (l, r)


(* Union *)
(* -------------------------- *)
(* If these don't overlap we include the middle, perhaps we don't want this? *)

(* Int *)
let iintr_union (iintr1 : int intr) (iintr2 : int intr) : int intr =
    match iintr1, iintr2 with
    | Intr ii1, Intr ii2 ->
        let { l = ii1l ; u = ii1u } = ii1 in
        let { l = ii2l ; u = ii2u } = ii2 in
        Intr { l = min_ints [ii1l ; ii2l]; u = max_ints [ii1u ; ii2u] }
    | IntrBot, _ | _, IntrBot -> IntrBot ;;

(* Float *)
let intr_union (intr1 : float intr) (intr2 : float intr) : float intr= 
    match intr1, intr2 with
    | Intr i1, Intr i2 ->
        let { l = i1l ; u = i1u } = i1 in
        let { l = i2l ; u = i2u } = i2 in
        Intr { l = min_flt [i1l ; i2l]; u = max_flt [i1u ; i2u] }
    | IntrBot, _ | _, IntrBot -> IntrBot ;;

(* Gets the sections of intr1 that don't overlap with intr2 *)
let intr_without (intr1 : float intr) (intr2 : float intr) : float intr list = 
    match intr1, intr2 with
    | Intr i1, Intr i2 ->
        filter (fun x -> x != IntrBot)
               (if i1.l < i2.l
                then [ intr_of_exc i1.l (min_flt [pred i2.l; i1.u]) ; intr_of_exc (succ i2.u) i1.u ]
                else [ intr_of_exc (max_flt [succ i2.u ; i1.l]) i1.u ])
    | IntrBot, _ -> [IntrBot]
    | _, IntrBot -> [intr1] ;;

(* section of i1 without any of is *)
let rec intr_withouts (i1 : float intr) (is : float intr list) : float intr list =
    intr_withouts_inner [i1] is
and intr_withouts_inner (acc : float intr list) (lst : float intr list) : float intr list =
    match lst with
    | x :: xs -> intr_withouts_inner (concat_map (fun i -> intr_without i x) acc) xs
    | [] -> acc

(* Get the section of i1 that overlaps with i2 *)
let intr_with (intr1 : float intr) (intr2 : float intr) : float intr =
    match intr1, intr2 with
    | Intr i1, Intr i2 -> intr_of_exc (max_flt [i1.l; i2.l]) (min_flt [i1.u; i2.u])
    | IntrBot, _ -> IntrBot
    | _, IntrBot -> intr1 ;;

(* First element of return is intr1 without any overlap of intr2.  Second element is
 * overlapping portion *)
let intr_partition (i1 : float intr) (i2 : float intr) 
    : (float intr list * float intr) = 
    (intr_without i1 i2, intr_with i1 i2) ;;

(* Get the intervals which meets the Sterbenz condition for i *)
let get_sterbenz_intr (intr : float intr) : float intr = 
    match intr with
    | Intr i ->
        let mul = intr_mul intr (intr_of_int 2) in
        let div = intr_div intr (intr_of_int 2) in
        (match mul, div with
         | Intr m, Intr d ->
             if contains intr 0.0 then IntrBot
             else if i.l >= 0. then
                 intr_of d.u m.l
             else if i.u <= 0. then
                 intr_of m.u d.l
             else IntrBot
                 (* raise (IntervalError "missing case when getting sterbenz_intervals")) *)
         | IntrBot, _ | _, IntrBot -> IntrBot)
    | IntrBot -> IntrBot ;;
