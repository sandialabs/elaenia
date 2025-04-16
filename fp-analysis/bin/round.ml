(* Import from https://github.com/tyabu12/ocaml-round *)
type round_mode =
  | NearestTiesToEven
  | ToZero
  | Up
  | Down
  (* | NearestTiesToAway *)

external add: round_mode -> float -> float -> float = "addc"
external sub: round_mode -> float -> float -> float = "subc"
external mul: round_mode -> float -> float -> float = "mulc"
external div: round_mode -> float -> float -> float = "divc"
external sqrt: round_mode -> float -> float = "sqrtc"
