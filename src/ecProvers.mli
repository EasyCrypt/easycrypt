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
type hints

module Hints : sig
  val empty : hints
  val full  : hints

  val add1 : path -> hints -> hints
  val addm : path -> hints -> hints
end

(* -------------------------------------------------------------------- *)
val execute_task : prover_infos -> hints -> Why3.Task.task -> bool option

val get_w3_th : string list -> string -> Why3.Theory.theory
