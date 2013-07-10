(* -------------------------------------------------------------------- *)
type ecloader

(* -------------------------------------------------------------------- *)
val create  : unit -> ecloader
val aslist  : ecloader -> (bool * string) list
val dup     : ecloader -> ecloader
val forsys  : ecloader -> ecloader
val addidir : ?system:bool -> string -> ecloader -> unit
val locate  : ?onlysys:bool -> string -> ecloader -> string option
