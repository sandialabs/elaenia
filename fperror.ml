(* Floating-Point Error Analysis Plugin *)

let help_msg = "Floating-point error analysis plugin for frama-c using FPTaylor"

module Self = Plugin.Register
  (struct
    let name = "Floating-point error analysis"
    let shortname = "fperror" let help = help_msg
  end)

let run () =
  try
    let chan = open_out "fperror.out" in
    Printf . fprintf chan "Hello, world!\n";
    flush chan;
    close_out chan
  with Sys_error _ as exc ->
    let msg = Printexc.to_string exc in
    Printf . eprintf "There was an error: %s\n" msg

let () = Db.Main.extend run
