(* -------------------------------------------------------------------- *)

type exn_printer = Format.formatter -> exn -> unit
val set_default : exn_printer -> unit
val register    : exn_printer -> unit
val exn_printer : exn_printer 




