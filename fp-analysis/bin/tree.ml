open Interval
open Stepfunction

open Segment
open List
open Util

(* Concrete Domain *)
type ctyp = IntTyp | FloatTyp | ArrTyp of ctyp ;;

type cval =
    | CInt   of int
    | CFloat of float
    | CArr   of (int -> cval) * int ;;
    (*
    | CIntArr   of (int -> int)
    | CFloatArr of (int -> float) ;;
    *)

type caexp =
    | CVal of cval
    | CVar of string * ctyp
    | CAcc of string * caexp option * ctyp (* Array Access *)
    | CAdd of caexp * caexp
    | CSub of caexp * caexp
    | CMul of caexp * caexp
    | CDiv of caexp * caexp ;;

type cbexp =
    | CLt of caexp * caexp
    | CLe of caexp * caexp
    | CEq of caexp * caexp
    | CNe of caexp * caexp
    | CGe of caexp * caexp
    | CGt of caexp * caexp ;;

type cstmt =
    | CAsgn of (string * caexp option) * caexp
    | CIf   of cbexp * cstmt * cstmt
    | CFor  of cstmt * cbexp * cstmt * cstmt
    | CCol  of cstmt * cstmt 
    | CRet  of caexp ;;

(* Abstract Domain *)

(* Abstract AST *)
type atyp = IntrTyp | AStepTyp | AArrTyp of atyp ;;

type aval = 
    | AInt   of int intr
    | AFloat of stepF 
    | AArr   of arr * int
    | ABot

and arr = (int, aval) Hashtbl.t ;;

type aaexp =
    | AVal of aval
    | AVar of string * atyp
    | AAcc of string * aaexp option * atyp (* array access *)
    | AAdd of aaexp * aaexp
    | ASub of aaexp * aaexp
    | AMul of aaexp * aaexp
    | ADiv of aaexp * aaexp ;;

type abexp =
    | ALt of aaexp * aaexp
    | ALe of aaexp * aaexp
    | AEq of aaexp * aaexp
    | ANe of aaexp * aaexp
    | AGe of aaexp * aaexp
    | AGt of aaexp * aaexp ;;

let not_abexp abexp = 
    match abexp with
    | ALt (l, r) -> AGe (l, r)
    | ALe (l, r) -> AGt (l, r)
    | AEq (l, r) -> ANe (l, r)
    | ANe (l, r) -> AEq (l, r)
    | AGe (l, r) -> ALt (l, r)
    | AGt (l, r) -> ALe (l, r) ;;

type astmt = 
    | AAsgn of (string * aaexp option) * aaexp
    | AIf   of abexp * astmt * astmt
    | AFor  of astmt * abexp * astmt * astmt
    | ACol  of astmt * astmt 
    | ARet  of aaexp ;;

(* Working with Arrays *)

let arr_bot () : (int, aval) Hashtbl.t = Hashtbl.create 5000 ;;

(* Apply a function piecewise to the elements of a1 and a2 for the length of
   the shorter list.  All elements in the longer list remain unchanged *)
let rec apply (f : aval -> aval -> aval)
              (a1 : arr) (l1 : int)
              (a2 : arr) (l2 : int) : aval =
    let (long, long_l), (_, short_l) = 
        if l1 < l2 
        then ((Hashtbl.copy a2, l2), (a1, l1))
        else ((Hashtbl.copy a1, l1), (a2, l2)) in
    iter (fun i -> match map2 f (Hashtbl.find_opt a1 i) 
                                (Hashtbl.find_opt a2 i) with
                   | Some av -> Hashtbl.replace long i av
                   | None    -> ())
         (int_seq short_l) ;
    AArr (long, long_l)

and map2 (f : 'a -> 'b -> 'c) (a : 'a option) (b : 'b option) : 'c option =
    match a, b with
    | Some av, Some bv -> Some (f av bv)
    | _, _ -> None ;;


let rec aval_union (intervals : int) (av1 : aval) (av2 : aval) : aval = 
    match av1, av2 with
    | AInt ii1, AInt ii2     -> AInt (iintr_union ii1 ii2)
    | AInt ii, AFloat et     -> AInt (iintr_union ii (sf_to_iintr et))
    | AFloat et, AInt ii     -> AInt (iintr_union (sf_to_iintr et) ii)
    | AFloat et1, AFloat et2 -> AFloat (sf_union intervals et1 et2) 
    | AArr (a1, l1), AArr (a2, l2) -> apply (aval_union intervals) a1 l1 a2 l2
    | AArr _, _ | _, AArr _  -> failwith "union of array and number" 
    | ABot, _ -> av2
    | _, ABot -> av1 ;;


let arr_update (intervals : int) (a1 : arr) (idxs : int intr) (v : aval) : arr =
    (* For each element in the index 
       Update the index with the union if it is there 
       If not then just return the thing *)
    let new_tbl = Hashtbl.copy a1 in
    List.iter (fun i -> match Hashtbl.find_opt new_tbl i with
                        | Some av -> Hashtbl.replace new_tbl i ((aval_union intervals) v av)
                        | None -> Hashtbl.replace new_tbl i v) 
              (iintr_range idxs);
    new_tbl ;;

