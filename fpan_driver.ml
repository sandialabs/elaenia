(* Floating-Point Error Analysis Plugin *)

open Fpan_finder

let help_msg = "Floating-point error analysis plugin for frama-c using FPTaylor."

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

let run () =
  if Enabled.get () then
    (* Set up File (or console) I/O *)
    let output msg =
      let chan = (
        if Output_file.is_default ()
        then stdout
        else open_out (Output_file.get ()))
      in
      try
        (* Perform the analysis *)
        let fmt = Format.formatter_of_out_channel chan in
        Self.feedback ~level:2 "Searching for FLOPs...";
        Printf.fprintf chan "%s\n" msg;
        Visitor.visitFramacFileSameGlobals (new find_flops fmt) (Ast.get ());
        flush chan;
        close_out chan;
      with Sys_error _ as exc ->
        let msg = Printexc.to_string exc in
        Printf.eprintf "fpan: run: %s\n" msg
    in
    output "Running fpan..."

let () = Db.Main.extend run
