(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
val from_channel : ?gcstats:bool -> name:string -> in_channel -> terminal
val from_tty     : unit -> terminal
val from_emacs   : unit -> terminal
