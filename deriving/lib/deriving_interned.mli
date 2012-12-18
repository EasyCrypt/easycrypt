(* Interned strings *)

type t
val compare : t -> t -> int
val eq : t -> t -> bool
val intern : string -> t
val to_string : t -> string
val name : t -> string
