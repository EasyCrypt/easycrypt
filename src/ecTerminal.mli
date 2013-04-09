(* -------------------------------------------------------------------- *)
type terminal

type status = [
  | `ST_Ok
  | `ST_Failure of exn
]

(* -------------------------------------------------------------------- *)
val interactive : terminal -> bool
val next        : terminal -> EcParsetree.prog
val notice      : immediate:bool -> string -> terminal -> unit
val finish      : status -> terminal -> unit
val finalize    : terminal -> unit

(* -------------------------------------------------------------------- *)
val from_channel : name:string -> in_channel -> terminal
val from_tty     : unit -> terminal
val from_emacs   : unit -> terminal
