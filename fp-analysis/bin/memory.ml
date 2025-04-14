open List

open Segment
open Stepfunction
open Interval
open Tree

(* Abstract Memory *)
type id = Id of string | ArrElem of string * int intr | Const ;;

module SS = Set.Make(String) ;;

exception UndefinedVariableException of string ;;

(* Memory modeled as a function.  The domain is tracked. *)
type amem = {
    dom : SS.t ;
    tbl : (string, aval) Hashtbl.t ;
}

let fail_lookup (x : string) (m : (string, aval) Hashtbl.t) = 
    match Hashtbl.find_opt m x with
    | Some v -> v
    | None -> raise (UndefinedVariableException (x ^ " Is not assigned")) ;;

let amem_bot = { dom = SS.empty ; tbl = Hashtbl.create 5000 }
let lookup (m : amem) (x : string) : aval option = Hashtbl.find_opt m.tbl x ;;

let rec amem_update (intervals : int) (n : id) (v : aval) (m : amem) : amem = 
    let { dom = mdom ; tbl = tbl } = m in
    let new_tbl = Hashtbl.copy tbl in
    match n with 
    | Id id -> 
        Hashtbl.replace new_tbl id v ;
        { dom = SS.add id mdom ; 
          tbl = new_tbl }
    | ArrElem (id, idxs) -> (
        match lookup m id with
        | Some (AArr (arr, l)) -> (
            let updated = AArr ((arr_update intervals arr idxs v), update_len l idxs) in
            Hashtbl.replace new_tbl id updated ;
            { dom = SS.add id mdom ; 
              tbl = new_tbl })
        | None -> (
            let updated = AArr ((arr_update intervals (arr_bot ()) idxs v), (upper idxs) + 1) in
            Hashtbl.replace new_tbl id updated ;
            { dom = SS.add id mdom ;
              tbl = new_tbl })
        | Some av -> failwith ("Attempting to index a non-array"))
    | Const -> m 

and update_len (l : int) (itr : int intr) : int =
    if l > upper itr + 1 then l else upper itr + 1;;

(* 
 * Rename variable n1 with the name n2.  Used to deduplicate the return
 * variable in memory.  If n1 does not exist in memory, is an array index, or
 * is a constant then nothing is done. 
 *)
let amem_rename (intervals : int) (n1 : id) (n2 : string) (m : amem) : amem =
    let { dom = mdom ; tbl = tbl } = m in 
    let new_tbl = Hashtbl.copy tbl in
    match n1 with
    | Id id              ->
        match lookup m id with
        | Some av -> (
            Hashtbl.remove new_tbl id ;
            Hashtbl.add new_tbl n2 av ;
            { dom = (SS.add n2 (SS.remove id mdom)) ;
              tbl = new_tbl })
        | None -> m
    | _ -> m ;;

let amem_contains (m : amem) (n : string) : bool = 
    match lookup m n with
    | None -> false
    | _   -> true ;;

let amem_eq (m1 : amem) (m2 : amem) : bool =
    m1.dom = m2.dom && 
    fold_left (fun acc x -> acc && (lookup m1 x) = (lookup m2 x))
              true 
              (SS.elements m1.dom) ;;
