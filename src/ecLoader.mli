(* -------------------------------------------------------------------- *)
type idx_t
type ecloader

(* -------------------------------------------------------------------- *)
type kind = [`Ec | `EcA]

exception BadExtension of string

val getkind : string -> kind

(* -------------------------------------------------------------------- *)
type namespace = [ `System | `Named of string ]

val string_of_namespace : namespace -> string

(* -------------------------------------------------------------------- *)
val create  : unit -> ecloader
val aslist  : ecloader -> ((namespace option * string) * idx_t) list
val dup     : ecloader -> ecloader
val forsys  : ecloader -> ecloader
val addidir : ?namespace:namespace -> ?recursive:bool -> string -> ecloader -> unit

(* Replace the include path wholesale, [aslist] being its reader.
   [addidir] only ever grows the path, so this is what lets a caller
   come back to an earlier one. *)
val setidirs : ((namespace option * string) * idx_t) list -> ecloader -> unit
val locate  : ?namespaces:(namespace option) list -> string -> ecloader -> (namespace option * string * kind) option
