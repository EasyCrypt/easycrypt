(* -------------------------------------------------------------------- *)
open EcParsetree
open EcEnv

(* -------------------------------------------------------------------- *)
val bdep : env -> pgamepath -> psymbol -> int -> int-> string list -> int -> unit
