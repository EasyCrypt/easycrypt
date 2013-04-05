(* -------------------------------------------------------------------- *)
type exn_printer = Format.formatter -> exn -> unit

val register    : exn_printer -> unit
val exn_printer : exn_printer 
val tostring    : exn -> string
