(* -------------------------------------------------------------------- *)

(* Global / mutable EasyCrypt state that can be attached to an
 * environment - and shared by all the decendant of such an
 * environment. This state can be used to register notification
 * functions or global flags (e.g. profiling / tracing) *)
type gstate

(* -------------------------------------------------------------------- *)
val create : unit -> gstate
val from_flags : (string * bool) list -> gstate

(* -------------------------------------------------------------------- *)
val getflag : ?default:bool -> string -> gstate -> bool
val setflag : string -> bool -> gstate -> unit
