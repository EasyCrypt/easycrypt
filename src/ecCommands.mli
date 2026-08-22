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

(* -------------------------------------------------------------------- *)
(* Proof-state introspection and navigation, for the LLM front-ends
   ([EcLlmCore] and the REPL and MCP servers on top of it). Batch
   compilation needs none of it: it never asks what the open goals are,
   never walks between them, and never rewrites a proof's bullet state.

   [focus_goal] and [disable_repl_bullets] MUTATE the global context;
   every other val here is a query that leaves it alone. *)

(* One open subgoal, as [pp_tree] reports it. *)
type goal_entry = {
  (* 1-based position in the open-goal list. *)
  ge_index   : int;
  (* The focused goal -- always the one at index 1, EC's focus model
     keeping the focused goal at the head. *)
  ge_focused : bool;
  (* The goal's conclusion on one line, or its full body under [~all]. *)
  ge_text    : string;
}

(* Is a proof active in the current scope? *)
val in_proof : unit -> bool

(* Every open goal of the active proof, rendered, focused first (the
   order [open_handles] uses). [] when no proof is active. *)
val pp_tree : ?all:bool -> unit -> goal_entry list

(* Handles of the active proof's open goals, focused first; [] when no
   proof is active. Same goals as [pp_tree], unrendered. *)
val open_handles : unit -> EcCoreGoal.handle list

(* The active proof's environment, the one the DAG queries below read.
   It is immutable and cumulative, so a snapshot keeps answering for its
   own proof after [qed] has discarded it -- which is how COMMIT still
   reconstructs the structure of a finished proof. [None] when no proof
   is active. *)
val current_proofenv : unit -> EcCoreGoal.proofenv option

(* Proof-DAG navigation in the *active* proof; both answer emptily when
   no proof is active. Use [EcCoreGoal.children_of_handle] /
   [parent_of_handle] on a [current_proofenv] snapshot to query a proof
   other than the active one. *)
val children_of : EcCoreGoal.handle -> EcCoreGoal.handle list
val parent_of : EcCoreGoal.handle -> EcCoreGoal.handle option

(* MUTATES the context: rotates the active proof's focus onto the open
   goal at 1-based index [k], and pushes the result as a new undo level,
   so UNDO/REVERT roll the rotation back like any other step. Returns
   the number of open goals. *)
val focus_goal : int -> (int, string) result

(* MUTATES the context: turns bullet enforcement off for phrases typed
   at a prompt, by clearing the [strict_bullets] pragma and dropping the
   active proof's bullet stack. Spends no undo level. Returns the stack
   it dropped -- which COMMIT reads to pick bullet tokens that do not
   collide with the ones already open -- and [None] on the idempotent
   later calls, the stack being gone by then. *)
val disable_repl_bullets : unit -> EcBullets.stack option

(* -------------------------------------------------------------------- *)
val pragma_verbose : bool -> unit
val pragma_g_prall : bool -> unit
val pragma_check   : EcScope.Ax.proofmode -> unit

exception InvalidPragma of string

val apply_pragma : string -> unit
val apply_pragma_option : string -> unit
