(* -------------------------------------------------------------------- *)
type ecloader

(* -------------------------------------------------------------------- *)
val create  : unit -> ecloader
val dup     : ecloader -> ecloader
val addidir : string -> ecloader -> unit
val locate  : string -> ecloader -> string option
