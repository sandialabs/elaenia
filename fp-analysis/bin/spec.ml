(* Parse a specification file for the tool 
 * The file gives a variable and its range of values on a new line
 * Example:
 *
 * x = {[ -0.1 ; 9.3 ], 0.01}
 * y = {[ -8.2 ; -1.2], 0.0002}
 *)

open In_channel
open String
open Str
open List

open Interval
open Segment
open Tree
open Memory
open Util

exception SpecFileError of string ;;

let notempty s = s <> "" ;;

let rec input_lines (f : in_channel) : string list =
    match input_line f with
    | Some l -> l :: input_lines f
    | None -> [] ;;

let parse_intr (str : string) =
    let no_brackets = global_replace (regexp "[][]") "" str in
    let split = map trim (split_on_char ';' no_brackets) in
    intr_of (Float.of_string (nth split 0)) (Float.of_string (nth split 1)) ;;

let parse_seg (str : string) = 
    let no_parens = global_replace (regexp "[()]") "" str in
    let split = filter notempty (split_on_char ',' no_parens) in
    let intr = parse_intr (nth split 0) in
    seg_of_intr intr (Float.of_string (nth split 1)) ;;

let parse_stepF (str : string) : aval = 
    let no_braces = global_replace (regexp "[{}]") "" str in
    let seg_strs = filter notempty (map trim (split_on_char ')' no_braces)) in
    AFloat (StepF (map parse_seg seg_strs))

let parse_arr (str : string) (bnds : (int * int)) : aval =
    let sf = parse_stepF str in
    let new_tbl = arr_bot () in
    let low, high = bnds in
    List.iter (fun i -> Hashtbl.replace new_tbl i sf) (int_seq_lh low high) ;
    AArr (new_tbl, high - low)  ;;

let rec parse_aval (name : string) (v : string) : (string * aval) =
    let n = parse_name name in
    if is_arr name
    then (n, parse_arr v (get_indices name))
    else (n, parse_stepF v)

and parse_name (n : string) : string =
    nth (split_on_char '[' n) 0 

and is_arr (str : string) : bool = 
    String.contains str '['

and get_indices (str : string) : (int * int) =
    let no_braces = 
        (global_replace (regexp "]") "" (nth (split_on_char '[' str) 1)) in
    let split = split_on_char ',' no_braces in
    (int_of_string (nth split 0), int_of_string (nth split 1)) ;;

let parse_line (l : string) : (string * aval) = 
    let split = map trim (split_on_char '=' l) in
    parse_aval (nth split 0) (nth split 1)

(* Split the file by lines *)
(* grab each line and turn it into a value *)
let parse_spec_file (filename : string) (intervals : int) : amem = 
    let ic = open_in filename in
    fold_left (fun acc l -> 
        let (n, aval) = parse_line l in
        amem_update intervals (Id n) aval acc)
        amem_bot 
        (input_lines ic) 
    ;;
