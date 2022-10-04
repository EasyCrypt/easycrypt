(* -------------------------------------------------------------------- *)
type terminal

type status = [
  | `ST_Ok
  | `ST_Failure of exn
]

type loglevel = EcGState.loglevel

(* -------------------------------------------------------------------- *)
val interactive : terminal -> bool
val next        : terminal -> EcParsetree.prog
val notice      : immediate:bool -> loglevel -> string -> terminal -> unit
val finish      : status -> terminal -> unit
val finalize    : terminal -> unit
val setwidth    : terminal -> int -> unit

(* -------------------------------------------------------------------- *)
type progress = [ `Human | `Script | `Silent ]

val from_channel :
     ?gcstats:bool
  -> ?progress:progress
  -> name:string
  -> in_channel
  -> terminal

val from_tty   : unit -> terminal
val from_emacs : unit -> terminal
