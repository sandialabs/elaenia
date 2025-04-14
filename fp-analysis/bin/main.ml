open Interp
open Parse
open Memory
open Acsl

(* Command Line Arguments *)
let usage_msg = "analyze [-test] <file1> -f <function-name> -sf <spec-file>" ;;

let input_file = ref "" ;;
let fun_name = ref "" ;;
let testing = ref false ;;
let spec_file = ref "" ;;
let out_file = ref "" ;;
let csv = ref false ;;
let acsl = ref false ;;
let intervals = ref 10000 ;;

let anon_fun filename = input_file := filename ;;

let speclist =
    [
        ("-f", Arg.Set_string fun_name, "Specify function to analyze");
        ("-sf", Arg.Set_string spec_file, "Specify variable range file");
        ("-test", Arg.Set testing, "Run tests");
        ("-csv", Arg.Set csv, "Output to CSV");
        ("-acsl", Arg.Set acsl, "Output to ACSL");
        ("-out", Arg.Set_string out_file, "output filename");
        ("-ensures-intervals", Arg.Set_int intervals, "Maximum number of intervals per variable");
    ] ;;

let () = Arg.parse speclist anon_fun usage_msg ;;

let initialize_spec =
    if !spec_file = ""
    then amem_bot
    else Spec.parse_spec_file !spec_file !intervals

(* Running the analyzer *)
let analyze filename initial_mem = 
    Format.printf "parsed specfile\n" ;
    let cstmt = transform (parse_file filename) !fun_name in
    Format.printf "parsed\n" ;
    let astmt = abst_stmt cstmt in
    Format.printf "abstracted\n";
    abst_interp astmt initial_mem !intervals ;;

let write_file name mem initial_mem =
    let oc = open_out name in
    if !acsl
    then (Printf.fprintf oc "%s" (Acsl.acsl_amem mem initial_mem) ;
          Printf.fprintf oc "%s" (get_fun_decl (parse_file !input_file) !fun_name))
    else
        if !csv 
        then Printf.fprintf oc "%s" (Printing.csv_amem mem);;

let () =
    if !testing 
    then Test.runtests () 
    else
        let initial_mem = initialize_spec in
        let mem = (analyze !input_file initial_mem) in
        (* Format.printf "%s\n\n" (str_amem mem) ; *)
        write_file !out_file mem initial_mem ;;
