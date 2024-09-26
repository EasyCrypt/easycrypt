(* -------------------------------------------------------------------- *)
open EcPath

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
module Version : sig
  type version

  val to_string : version -> string
end

(* -------------------------------------------------------------------- *)
type coq_mode =
  | Check (* Check scripts *)
  | Edit  (* Edit then check scripts *)
  | Fix   (* Try to check script, then edit script on non-success *)

(* -------------------------------------------------------------------- *)
type prover_eviction = [
  | `Inconsistent
]

type prover = {
  pr_name    : string;
  pr_version : Version.version;
  pr_alt     : string;
  pr_evicted : (prover_eviction * bool) option;
}

type prover_infos = {
  pr_maxprocs  : int;
  pr_provers   : string list;
  pr_timelimit : int;
  pr_cpufactor : int;
  pr_quorum    : int;
  pr_verbose   : int;
  pr_all       : bool;
  pr_max       : int;
  pr_iterate   : bool;
  pr_wanted    : hints;
  pr_unwanted  : hints;
  pr_dumpin    : string EcLocation.located option;
  pr_selected  : bool;
  gn_debug     : bool;
}

val dft_prover_infos : prover_infos
val dft_prover_names : string list

val known : evicted:bool -> prover list

(* -------------------------------------------------------------------- *)
type parsed_pname = {
  prn_name     : string;
  prn_alt      : string;
  prn_version  : Version.version option;
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
type notify = EcGState.loglevel -> string Lazy.t -> unit

val maybe_start_why3_server : prover_infos -> unit

val execute_task : ?notify:notify -> prover_infos -> Why3.Task.task -> bool option
val get_w3_th : string list -> string -> Why3.Theory.theory

val get_w3_main : unit -> Why3.Whyconf.main
val get_w3_env : unit -> Why3.Env.env
val get_w3_conf : unit -> Why3.Whyconf.config
