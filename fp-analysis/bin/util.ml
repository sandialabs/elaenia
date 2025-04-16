open List

(* product_map f [a1; ...; an] [b1; ...; bm] = 
   [f a1 b1; f a1 b2; ... f a2 b1 ; f a2 b2 ; ... ; f an bm] *)
let product_map (f : 'a -> 'b -> 'c) (xs : 'a list) (ys : 'b list) : 'c list = 
    let ret = concat_map (fun x -> 
        map (fun y -> f x y) ys) xs in
    ret ;;

let min_ints l = List.fold_left Int.min Int.max_int l ;;
let max_ints l = List.fold_left Int.max Int.min_int l ;;

let min_flt l = List.fold_left Float.min infinity l ;;
let max_flt l = List.fold_left Float.max neg_infinity l ;;

(* Ulp function *)
let ulp f = Float.succ f -. f ;;

(* Get the smallest divisor of a number that does not produce infinity *)
let smallest_finite_divisor (f : float) : float =
    f /. Float.max_float ;;

let fail_unwrap op =
    match op with
    | Some v -> v
    | None -> failwith "Unwrapped empty option" 
    ;;

let last lst = nth lst ((length lst) - 1) ;;
let rec remove_last lst = 
    match lst with
    | [] -> []
    | _ :: [] -> []
    | x :: xs -> x :: (remove_last xs) ;;

(* Get optional value with default *)
let get_opt (x : 'a option) (default : 'a) : 'a =
    match x with
    | Some v -> v
    | None   -> default ;;

(* Map the optional or return a default value *)
let map_opt (f : 'a -> 'b) (x : 'a option) (default : 'b) : 'b =
    match x with
    | Some v -> f v
    | None   -> default ;;

(* Create a list of sequential numbers from l to h *)
let int_seq_lh l h = List.init (h - l) (fun x -> l + x) ;;

(* Create a list of sequential numbers of length l starting from 0 *)
let int_seq l = List.init l (fun x -> x) ;;

