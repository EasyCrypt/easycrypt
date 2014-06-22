(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
open EcPath

(* -------------------------------------------------------------------- *)
type prover_infos = {
  pr_maxprocs  : int;
  pr_provers   : string list;
  pr_timelimit : int;
  pr_wrapper   : string option;
}

val dft_prover_infos : prover_infos
val dft_prover_names : string list

val known_provers : unit -> string list
val is_prover_known : string -> bool

(* -------------------------------------------------------------------- *)
val initialize : string option -> unit

(* -------------------------------------------------------------------- *)
type hflag = [ `Include | `Exclude ]
type hints

module Hints : sig
  val empty : hints
  val full  : hints

  val add1 : path -> hflag -> hints -> hints
  val addm : path -> hflag -> hints -> hints

  val mem : path -> hints -> bool
end

(* -------------------------------------------------------------------- *)
val execute_task : prover_infos -> Why3.Task.task -> bool option

val get_w3_th : string list -> string -> Why3.Theory.theory
