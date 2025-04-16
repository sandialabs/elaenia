open Util
open Interr

(* Determining error propagation from operations *)
let ulp_add l r = 0.5 *. ulp ((abs l.int.u) +. (abs r.int.u) +. l.err +. r.err) ;;
let ulp_sub l r = 0.5 *. ulp ((mag_lg l.int) +. (mag_lg r.int) +. l.err +. r.err) ;;
let ulp_mul l r = 
    0.5 *. ulp (((mag_lg l.int) +. l.err) *. ((mag_lg r.int) +. r.err)) ;;
let ulp_div l r = 
    0.5 *. ulp (((mag_lg l.int) +. l.err) /. ((mag_sm r.int) +. r.err)) ;;

let err_add l r = 
    match l.err, r.err with
    | le, re when not (is_finite le) || not (is_finite re) -> infinity
    | le, re -> le +. re +. ulp_add l r ;;

let err_sub l r = abs (l.err +. r.err) +. ulp_sub l r ;;

let err_mul l r =
    let lup = mag_lg l.int in
    let rup = mag_lg r.int in
    lup *. r.err +. rup *. l.err +. l.err *. r.err +. ulp_mul l r ;;

let err_div l r =
    let lup = mag_lg l.int in
    let rup = mag_lg r.int in
    ((rup *. l.err -. lup *. r.err) /. (rup *. rup +. rup *. r.err)) +.
    ulp_div l r ;;
