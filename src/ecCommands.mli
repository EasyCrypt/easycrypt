(* -------------------------------------------------------------------- *)
open EcLocation

(* -------------------------------------------------------------------- *)
exception Restart

(* -------------------------------------------------------------------- *)
type loader

val loader   : loader
val addidir  : ?namespace:EcLoader.namespace -> ?recursive:bool -> string -> unit
val loadpath : unit -> (EcLoader.namespace option * string) list

(* -------------------------------------------------------------------- *)
type notifier = EcGState.loglevel -> string Lazy.t -> unit

type checkmode = {
  cm_checkall : bool;
  cm_timeout  : int;
  cm_cpufactor: int;
  cm_nprovers : int;
  cm_provers  : string list option;
  cm_profile  : bool;
  cm_iterate  : bool;
}

val initial : checkmode:checkmode -> boot:bool -> checkproof:bool -> EcScope.scope

val initialize  :
     restart:bool
  -> undo:bool
  -> boot:bool
  -> checkmode:checkmode
  -> checkproof:bool
  -> unit

val current     : unit -> EcScope.scope
val addnotifier : notifier -> unit
val notify      : EcGState.loglevel -> ('a, Format.formatter, unit, unit) format4 -> 'a

(* -------------------------------------------------------------------- *)
val process_internal :
     loader
  -> EcScope.scope
  -> EcParsetree.global_action located
  -> EcScope.scope

(* -------------------------------------------------------------------- *)
val process : ?src:string -> ?timed:bool -> ?break:bool ->
  EcParsetree.global_action located -> float option

val undo  : int  -> unit
val reset : unit -> unit
val uuid  : unit -> int
val mode  : unit -> string

val check_eco : string -> bool

val doc_comment : [`Global | `Item] * string -> unit

(* -------------------------------------------------------------------- *)
val pp_current_goal : ?all:bool -> Format.formatter -> unit
val pp_maybe_current_goal : Format.formatter -> unit
val pp_all_goals : unit -> string list

(* -------------------------------------------------------------------- *)
val pragma_verbose : bool -> unit
val pragma_g_prall : bool -> unit
val pragma_check   : EcScope.Ax.proofmode -> unit

exception InvalidPragma of string

val apply_pragma : string -> unit
