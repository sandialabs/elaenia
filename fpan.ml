(* Floating-Point Error Analysis Plugin *)

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
  try
  if Enabled.get () then
    (* Set up File (or console) I/O *)
    let outfile = Output_file.get () in
    let output msg analysis =
      if Output_file.is_default () then
        Self.result "%s" (msg ^ "\n" ^ analysis)
      else
        let chan = open_out outfile in
        Printf.fprintf chan "%s\n%s\n" msg analysis;
        flush chan;
        close_out chan;
    in
    (* Perform the analysis *)
    let analysis =
      Self.feedback ~level:2 "Computing 0.1 * 0.2...";
      0.1 *. 0.2
    in
    (* Output analysis *)
    output "Running fpan..." (Printf.sprintf "%h" analysis)
  with Sys_error _ as exc ->
    let msg = Printexc.to_string exc in
    Printf.eprintf "fpan: run: %s\n" msg

let () = Db.Main.extend run
