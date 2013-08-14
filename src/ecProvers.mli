(* -------------------------------------------------------------------- *)
type prover_infos = {
  pr_maxprocs  : int;
  pr_provers   : string list;
  pr_timelimit : int;
}

val dft_prover_infos : prover_infos
val dft_prover_names : string list

(* -------------------------------------------------------------------- *)
val call_prover_task : prover_infos -> Why3.Task.task -> bool option

val check_prover_name : string -> bool

val get_w3_th : string list -> string -> Why3.Theory.theory

val initialize : string option -> unit

val known_provers : unit -> string list
