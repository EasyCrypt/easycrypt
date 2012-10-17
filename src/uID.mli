(** Provides Unique identifiers for different object kinds.
* The identifiers can be compared using Pervasives.compare standard function.
*)

(** Unique identifier for operators *)
type op
val fresh_op : string -> op
val int_of_op : op -> int
(** Unique identifier for variables based on variable name *)
type var = int
val fresh_var : string -> var

(** different from any [fresh_var] *)
val neq_var : var

val pp_var : Format.formatter -> var -> unit

(** Unique identifier for logic (Fol) variables *)
type lvar 
(** This is a special identifier for the free logic variable that reprent the
* program one. *)
val empty_lvar : lvar
val fresh_lvar : var option -> lvar
val pp_lvar : Format.formatter -> lvar -> unit

(** Unique identifier for type variables based on type name *)

type tvar
val fresh_tvar : string -> tvar
val pp_tvar : Format.formatter -> tvar -> unit


