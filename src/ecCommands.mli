(* -------------------------------------------------------------------- *)
open EcLocation

(* -------------------------------------------------------------------- *)
exception Restart

(* -------------------------------------------------------------------- *)
type loader

val loader : loader
val addidir : ?namespace:EcLoader.namespace -> ?recursive:bool -> string -> unit
val loadpath : unit -> (EcLoader.namespace option * string) list
val set_current_path : string -> unit

(* An opaque record of the include path at one point in time.
   [loadpath_reset] puts the loader back to it, dropping every
   directory added since. The include path is process-global and
   [addidir] only ever grows it, so this is the only way to keep one
   loaded file's directory out of an unrelated later load. *)
type loadpath_mark

val loadpath_mark  : unit -> loadpath_mark
val loadpath_reset : loadpath_mark -> unit

(* -------------------------------------------------------------------- *)
type notifier = EcGState.loglevel -> string Lazy.t -> unit

type checkmode = {
  cm_checkall : bool;
  cm_timeout  : int;
  cm_cpufactor: int;
  cm_nprovers : int;
  cm_provers  : string list option;
  cm_quorum   : int option;
  cm_profile  : bool;
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

(* Redirect the [print] statement's output. It goes to the process's
   stdout by default; a front-end that frames its replies installs a
   formatter it can read back, so that [print] lands inside the frame
   the way [search] and [locate] already do. The formatter is flushed
   after every [print]. *)
val set_print_formatter : Format.formatter -> unit

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

(* An opaque snapshot of the engine's undo context: current scope, undo
   stack and uuid. [undo] only pops, so it cannot undo an [undo] --
   input that lowered the uuid before failing lands somewhere else
   entirely. [undo_restore] puts the engine back exactly, forward as
   well as backward. Pragmas and the printing state are global and
   outside the context, as they already are for [undo]. *)
type undo_mark

val undo_mark    : unit -> undo_mark
val undo_restore : undo_mark -> unit
val uuid  : unit -> int
val mode  : unit -> string

val check_eco : string -> bool

val doc_comment : [`Global | `Item] * string -> unit

(* -------------------------------------------------------------------- *)
val pp_current_goal : ?all:bool -> Format.formatter -> unit
val pp_current_goal_or_noproof : ?all:bool -> Format.formatter -> unit
val pp_maybe_current_goal : Format.formatter -> unit
val pp_all_goals : unit -> string list
val in_proof : unit -> bool
val disable_repl_bullets : unit -> EcBullets.stack option
val pp_tree : ?all:bool -> unit -> (int * bool * string) list
val focus_goal : int -> (int, string) result
val open_handles : unit -> EcCoreGoal.handle list
val current_proofenv : unit -> EcCoreGoal.proofenv option
val children_of : EcCoreGoal.handle -> EcCoreGoal.handle list
val parent_of : EcCoreGoal.handle -> EcCoreGoal.handle option

(* -------------------------------------------------------------------- *)
val pragma_verbose : bool -> unit
val pragma_g_prall : bool -> unit
val pragma_check   : EcScope.Ax.proofmode -> unit

exception InvalidPragma of string

val apply_pragma : string -> unit
val apply_pragma_option : string -> unit
