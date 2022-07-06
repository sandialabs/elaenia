(* Fpan: Floating-Point Error Analysis Plugin *)

open Fpan_finder_fptaylor
open Fpan_finder_gappa

let help_msg = "Floating-point error analysis plugin for frama-c."

module Self = Plugin.Register
  (struct
    let name = "FP Analyzer"
    let shortname = "fpan"
    let help = help_msg
  end)

module Enabled = Self.False
  (struct
    let option_name = "-fpan"
    let help = "when on (off by default), run" ^ help_msg
  end)

module Output_file = Self.String
  (struct
    let option_name = "-fpan-output"
    let default = "-"
    let arg_name = "output-file"
    let help = "file where the analysis is output (default: output to console)"
  end)

exception Invalid_backend of string
module Backend = Self.String
  (struct
    let option_name = "-fpan-backend"
    let arg_name = "backend"
    let default = "fptaylor"
    let help = "Backend for analysis (options: gappa, fptaylor)\n\
               (default: fptaylor)"
  end)

let run () =
  if Enabled.get () then
    (* Set up File (or console) I/O *)
    let output msg =
      let chan = (
        if Output_file.is_default ()
        then stdout
        else open_out (Output_file.get ())
      ) in
      try
        (* Validate backend argument *)
        let fmt = Format.formatter_of_out_channel chan in
        let ff = (
          match (String.lowercase_ascii (Backend.get ())) with
          | "fptaylor" -> (new find_flops_fptaylor fmt)
          | "gappa"    -> (new find_flops_gappa fmt)
          | _          -> raise (Invalid_backend (Backend.get ()))
        ) in
        Self.feedback ~level:2 "Searching for FLOPs...";
        Printf.fprintf chan "%s\n" msg;
        (* Perform the analysis *)
        Visitor.visitFramacFileSameGlobals ff (Ast.get ());
        flush chan;
        close_out chan;
      with
        | Sys_error _ as exc ->
          let msg = Printexc.to_string exc in
          Printf.eprintf "fpan: run: %s\n" msg
        | Invalid_backend b ->
          Printf.eprintf "fpan: run: improper backend '%s'\n" b
    in
    output "Running fpan..."

let () = Db.Main.extend run
