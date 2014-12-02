(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcPath

(* -------------------------------------------------------------------- *)
type prover_eviction = [
  | `Inconsistent
]

type prover = {
  pr_name    : string;
  pr_version : string;
  pr_evicted : (prover_eviction * bool) option;
}

type prover_infos = {
  pr_maxprocs  : int;
  pr_provers   : string list;
  pr_timelimit : int;
  pr_cpufactor : int;
  pr_wrapper   : string option;
}

val dft_prover_infos : prover_infos
val dft_prover_names : string list

val known : evicted:bool -> prover list

(* -------------------------------------------------------------------- *)
type parsed_pname = {
  prn_name     : string;
  prn_ovrevict : bool;
}

val parse_prover_name : string -> parsed_pname
val is_prover_known   : string -> bool

(* -------------------------------------------------------------------- *)
val initialize :
     ?ovrevict:string list
  -> ?why3conf:string
  -> unit -> unit

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
type notify = EcGState.loglevel -> string Lazy.t -> unit

val execute_task : ?notify:notify -> prover_infos -> Why3.Task.task -> bool option
val get_w3_th : string list -> string -> Why3.Theory.theory
