(* Floating-Point Error Analysis Plugin *)

let help_msg = "Floating-point error analysis plugin for frama-c using FPTaylor"

module Self = Plugin.Register
  (struct
    let name = "FP Analyzer"
    let shortname = "fpan"
    let help = help_msg
  end)

let run () =
  let product =
    Self . feedback ~level:2 "Computing 0.1 * 0.2...";
    0.1 *. 0.2
  in
  Self . result "0.1 * 0.2 = %h" product

let () = Db.Main.extend run
