(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath

(* -------------------------------------------------------------------- *)
(* Proof-local simplify context: the set of active simplify databases,
   proof-local defaults (database / head filter) and the per-database
   overlay of locally added user-reduction rules. *)

type entry = path * EcTheory.rule

(* A head filter restricts user-reduction rules to (or away from) those
   whose left-hand side is headed by one of the given symbols. *)
type head_mode = [`Include | `Exclude]
type head_filter = [`Include of Sp.t | `Exclude of Sp.t]

(* Canonical name of the default simplify database (the empty name). *)
val dname : symbol

type simplify_context

val empty : simplify_context

val active : simplify_context -> Ssym.t
(* Proof-local default databases for bare [simplify]/[cbv]: [None] means
   no local default, [Some dbs] means consult exactly [dbs]. *)
val default_db : simplify_context -> symbol list option
val default_hd : simplify_context -> head_filter option

val activate : symbol list -> simplify_context -> simplify_context
val deactivate : symbol list -> simplify_context -> simplify_context

val set_default_db : symbol list -> simplify_context -> simplify_context
val set_default_hd :
  (head_mode * path list) option -> simplify_context -> simplify_context
val clear_default : simplify_context -> simplify_context

val added : ?base:symbol -> simplify_context -> entry list

val add_rules : ?base:symbol -> entry list -> simplify_context -> simplify_context
val clear : ?base:symbol -> simplify_context -> simplify_context
