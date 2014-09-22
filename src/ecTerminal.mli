(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
type terminal

type status = [
  | `ST_Ok
  | `ST_Failure of exn
]

(* -------------------------------------------------------------------- *)
val interactive : terminal -> bool
val next        : terminal -> EcParsetree.prog EcLocation.located
val notice      : immediate:bool -> string -> terminal -> unit
val finish      : status -> terminal -> unit
val finalize    : terminal -> unit

(* -------------------------------------------------------------------- *)
val from_channel : name:string -> in_channel -> terminal
val from_tty     : unit -> terminal
val from_emacs   : unit -> terminal
