(* -------------------------------------------------------------------- *)
type ecreader

(* -------------------------------------------------------------------- *)
val from_channel : name:string -> in_channel -> ecreader
val from_file    : string -> ecreader
val from_string  : string -> ecreader

(* -------------------------------------------------------------------- *)
val finalize : ecreader -> unit
val parse    : ecreader -> EcParsetree.prog * bool
val parseall : ecreader -> EcParsetree.prog
