(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcLocation

(* -------------------------------------------------------------------- *)
exception Restart

(* -------------------------------------------------------------------- *)
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

val initialize  :
     restart:bool
  -> undo:bool
  -> boot:bool
  -> checkmode:checkmode
  -> unit

val current     : unit -> EcScope.scope
val addnotifier : notifier -> unit

(* -------------------------------------------------------------------- *)
val process : ?timed:bool -> ?break:bool ->
  EcParsetree.global_action located -> float option

val undo  : int  -> unit
val reset : unit -> unit
val uuid  : unit -> int
val mode  : unit -> string

val check_eco : string -> bool

(* -------------------------------------------------------------------- *)
val pp_current_goal : ?all:bool -> Format.formatter -> unit
val pp_maybe_current_goal : Format.formatter -> unit

(* -------------------------------------------------------------------- *)
val pragma_verbose : bool -> unit
val pragma_g_prall : bool -> unit
val pragma_check   : EcScope.Ax.mode -> unit

exception InvalidPragma of string

val apply_pragma : string -> unit
