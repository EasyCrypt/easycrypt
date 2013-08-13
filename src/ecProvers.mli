type prover_infos =
  { prover_max_run   : int;
    prover_names     : string array;
    prover_timelimit : int; }

val call_prover_task : prover_infos -> Why3.Task.task -> bool

val dft_prover_infos : prover_infos

val check_prover_name : string -> bool

val get_w3_th : string list -> string -> Why3.Theory.theory

val initialize : string option -> unit

val known_provers : unit -> string list
