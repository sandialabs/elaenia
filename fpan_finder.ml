(** FPan Floating-Point Operation Finder *)

open Cil_types

let print_stmt out = function
  | Instr i -> Printer.pp_instr out i
  | _       -> Printer.pp_binop out PlusA
(* | _       -> Printer.pp_binop out PlusA (TFloat(FDouble,[])) *)

class find_flops out = object
  inherit Visitor.frama_c_inplace

  method! vfile _ =
    Format.fprintf out "@[< hov 2> digraph {@ ";
    Cil.DoChildrenPost (fun f -> Format.fprintf out "}@]@."; f)
  
  method! vglob_aux g =
    match g with
    | GFun(f,_) ->
      Format.fprintf out "@[< hov 2> subgraph cluster_%a {@ \
                          @[< hv 2> graph@ [label=\"%a\"];@]@ "
          Printer.pp_varinfo f.svar
          Printer.pp_varinfo f.svar;
      Cil.DoChildrenPost(fun g -> Format.fprintf out "}@]@ "; g)
    | _ -> Cil.SkipChildren
  
  method! vstmt_aux s =
    Format.fprintf out "@[< hov 2> s%d@ [label=%S]@];@ "
      s.sid (Pretty_utils.to_string print_stmt s.skind);
    List.iter
      (fun succ -> Format.fprintf out "@[s%d -> s%d;@]@ " s.sid succ.sid)
      s.succs;
    Format.fprintf out "@]"; Cil .DoChildren
end

