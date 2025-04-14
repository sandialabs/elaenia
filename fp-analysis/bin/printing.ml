open List

open Tree
open Interval
open Segment
open Stepfunction
open Memory
open Util

let flt_fmt f = Format.sprintf "%40.50f" f ;;

(* Concrete Domain *)
let str_cval (v : cval) : string =
    match v with
    | CInt i      -> Int.to_string i
    | CFloat f    -> Float.to_string f 
    | CArr (_, _) -> "arr" ;;
    (*
    | CIntArr a   -> "int[]"
    | CFloatArr a -> "flt[]"
    ;;
    *)

let rec str_caexp (exp : caexp) : string = 
    match exp with
    | CVal v         -> str_cval v
    | CVar (n, _)    -> n
    | CAcc (n, i, _) -> n ^ "[" ^ map_opt str_caexp i "" ^ "]"
    | CAdd (l, r)    -> str_caexp l ^ " + " ^ str_caexp r
    | CSub (l, r)    -> str_caexp l ^ " - " ^ str_caexp r
    | CMul (l, r)    -> str_caexp l ^ " * " ^ str_caexp r
    | CDiv (l, r)    -> str_caexp l ^ " / " ^ str_caexp r ;;

let str_cbexp (exp : cbexp) : string =
    match exp with
    | CLt (l, r) -> str_caexp l ^ " < "  ^ str_caexp r
    | CLe (l, r) -> str_caexp l ^ " <= " ^ str_caexp r
    | CEq (l, r) -> str_caexp l ^ " = "  ^ str_caexp r
    | CNe (l, r) -> str_caexp l ^ " != " ^ str_caexp r
    | CGe (l, r) -> str_caexp l ^ " >= "  ^ str_caexp r
    | CGt (l, r) -> str_caexp l ^ " > " ^ str_caexp r ;;

let rec str_cstmt (stmt : cstmt) : string = 
    match stmt with
    | CAsgn ((n, i), v) -> 
        n ^ map_opt (fun x -> "[" ^ str_caexp x ^ "]") i "" ^ " = " ^ str_caexp v
    | CIf (b, t, e) -> 
        "if (" ^ str_cbexp b ^ ")\nthen " ^ str_cstmt t ^ "\nelse " ^ str_cstmt e
    | CFor (i, c, a, b) ->
        "for (" ^ str_cstmt i ^ "; " ^ str_cbexp c ^ "; " ^ str_cstmt a ^ ")\n" ^
        str_cstmt b
    | CCol (f, s) -> str_cstmt f ^ ";\n" ^ str_cstmt s 
    | CRet aexp ->
        "return " ^ str_caexp aexp ^ ";"
    ;;

(* Abstract Domain *)
let str_interval (i : float interval) : string = 
    "[" ^ flt_fmt i.l ^ 
    " ; " ^ flt_fmt i.u ^ "]" ;;

let str_intr (intr : float intr) : string =
    match intr with
    | Intr i -> str_interval i
    | IntrBot -> "_|_" ;;

let str_intrs (is : float intr list) : string =
    fold_left (fun acc i -> acc ^ str_intr i ^ ", ") "{" is ^ "}" ;;

let str_iInterval (i : int interval) : string =
        "[" ^ Int.to_string i.l ^ 
        " ; " ^ Int.to_string i.u ^ "]" ;;

let str_iIntr (intr : int intr) : string =
    match intr with
    | Intr i -> str_iInterval i
    | IntrBot -> "_|_" ;;

let str_seg (seg : segment) : string =
    "(" ^ str_intr seg.int ^ ", " ^ flt_fmt seg.err ^ ")" ;;

let str_segs (segs : segment list) : string =
    fold_left (fun acc s -> acc ^ str_seg s ^ ", ") "{" segs ^ "}" ;;

let str_sf (trm : stepF) : string = 
    match trm with
    | StepF ies -> str_segs ies
    | Bot       -> "_" ;;

let str_id (id : id) : string = 
    match id with
    | Id n -> n
    | Const -> "Const" 
    | ArrElem (n, idxs) -> n ^ "[" ^ str_iIntr idxs ^ "]" ;;

let rec str_aval (v : aval) : string =
    match v with
    | AInt i      -> str_iIntr i
    | AFloat Bot  -> "_|_"
    | AFloat trm  -> str_sf trm 
    | AArr (tbl, l) -> 
        (fold_left (fun acc i -> acc ^ (Int.to_string i) ^ " : " ^ 
                                 str_aval (Hashtbl.find tbl i) ^ ", ")
                   ("[")
                   (init l (fun x -> x))) ^ "] (" ^ Int.to_string l ^ ")" 
    | ABot -> "ABot" ;;

let rec str_aaexp (exp : aaexp) : string = 
    match exp with
    | AVal v         -> str_aval v
    | AVar (n, _)    -> n
    | AAcc (n, i, _) -> n ^ "[" ^ map_opt str_aaexp i "" ^ "]"
    | AAdd (l, r)    -> str_aaexp l ^ " + " ^ str_aaexp r
    | ASub (l, r)    -> str_aaexp l ^ " - " ^ str_aaexp r
    | AMul (l, r)    -> str_aaexp l ^ " * " ^ str_aaexp r
    | ADiv (l, r)    -> str_aaexp l ^ " / " ^ str_aaexp r ;;

let str_abexp (exp : abexp) : string =
    match exp with
    | ALt (l, r) -> str_aaexp l ^ " < "  ^ str_aaexp r
    | ALe (l, r) -> str_aaexp l ^ " <= " ^ str_aaexp r
    | AEq (l, r) -> str_aaexp l ^ " = "  ^ str_aaexp r
    | ANe (l, r) -> str_aaexp l ^ " != " ^ str_aaexp r
    | AGe (l, r) -> str_aaexp l ^ " >= "  ^ str_aaexp r
    | AGt (l, r) -> str_aaexp l ^ " > " ^ str_aaexp r ;;

let rec str_astmt (stmt : astmt) : string = 
    match stmt with
    | AAsgn ((n, i), v) -> 
        n ^ map_opt (fun x -> "[" ^ str_aaexp x ^ "]") i "" ^ " = " ^ str_aaexp v
    | AIf (b, t, e) -> 
        "if " ^ str_abexp b ^ "\nthen " ^ str_astmt t ^ "\nelse " ^ str_astmt e
    | AFor (i, c, a, b) ->
        "for (" ^ str_astmt i ^ "; " ^ str_abexp c ^ "; " ^ str_astmt a ^ ")\n" ^
        str_astmt b
    | ACol (f, s) -> str_astmt f ^ ";\n" ^ str_astmt s 
    | ARet aexp -> "return " ^ str_aaexp aexp ^ ";" ;;

let str_avar (n : string) (amem : amem) : string = 
    match lookup amem n with
    | Some av -> n ^ " -> " ^ str_aval av
    | None -> n ^ " -> _" ;;

let str_amem (amem : amem) : string =
    fold_left (fun acc x -> acc ^ "\n" ^ (str_avar x amem))
              "" (SS.elements amem.dom) ;;

(* For CSV output *)
let csv_interval (i : float interval) : string = 
    "[" ^ Format.sprintf "%f" i.l ^ 
    " ; " ^ Format.sprintf "%f" i.u ^ "]" ;;

let csv_intr (intr : float intr) : string =
    match intr with
    | Intr i -> csv_interval i
    | IntrBot -> "_|_" ;;

let csv_iInterval (i : int interval) : string =
    Int.to_string i.l ^ "," ^ Int.to_string i.u ^ ",0.0";;

let csv_iIntr (intr : int intr) : string =
    match intr with
    | Intr i -> csv_iInterval i
    | IntrBot -> "IntrBot,IntrBot,0.0" ;;

let csv_seg (seg : segment) :  string =
    match seg.int with
    | Intr i ->
        Format.sprintf "%20.30e" i.l ^ "," ^
        Format.sprintf "%20.30e" i.u ^ "," ^
        Format.sprintf "%20.30e" seg.err
    | _ ->
        Format.sprintf "_|_" ^ "," ^
        Format.sprintf "_|_" ^ "," ^
        Format.sprintf "%20.30e" seg.err
    ;;

let csv_segs (name : string) (segs : segment list) : string =
    fold_left (fun acc s -> acc ^ name ^ ",flt," ^ csv_seg s ^ "\n") "" segs ;;

let csv_sf (name : string) (trm : stepF) : string = 
    match trm with
    | StepF ies -> csv_segs name ies
    | Bot       -> name ^ ",flt,Bot,Bot,0.0" ;;

let rec csv_aval (n : string) (av : aval) : string = 
    match av with 
    | AInt ii      -> n ^ ",int," ^ csv_iIntr ii
    | AFloat et    -> csv_sf n et
    | AArr (ar, l) -> csv_arr n ar l
    | ABot         -> n ^ ",bot,-,-,-"

and csv_arr (n : string) (ar : (int, aval) Hashtbl.t) (l : int) : string =
    fold_left (fun acc i -> 
              Format.printf "csv_arr %d\n" i ;
               acc ^ (csv_aval (n ^ "[" ^ Int.to_string i ^ "]") (Hashtbl.find ar i) ^ "\n"))
              ""
              (int_seq l) ;;

let csv_avar (n : string) (amem : amem) : string = 
    match (lookup amem n) with
    | Some av -> csv_aval n av
    | None -> n ^ " -> _" ;;

let csv_amem (amem : amem) : string =
    fold_left (fun acc x -> acc ^ (csv_avar x amem) ^ "\n")
              "var,type,low,high,err\n" (SS.elements amem.dom) ;;
