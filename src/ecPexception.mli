(* -------------------------------------------------------------------- *)
open EcTypedtree

type exn_printer = Format.formatter -> exn -> unit
val set_default : exn_printer -> unit
val register    : exn_printer -> unit
val exn_printer : exn_printer 


(* -------------------------------------------------------------------- *)
val pp_typerror : Format.formatter -> tyerror -> unit

(* -------------------------------------------------------------------- *)
val pp_exn : Format.formatter -> exn -> unit

