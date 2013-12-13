(* -------------------------------------------------------------------- *)
type idx_t
type ecloader

(* -------------------------------------------------------------------- *)
val create  : unit -> ecloader
val aslist  : ecloader -> ((bool * string) * idx_t) list
val dup     : ecloader -> ecloader
val forsys  : ecloader -> ecloader
val addidir : ?system:bool -> ?recursive:bool -> string -> ecloader -> unit
val locate  : ?onlysys:bool -> string -> ecloader -> string option
