(* -------------------------------------------------------------------- *)
exception Interrupted

(* -------------------------------------------------------------------- *)
val addidir : string -> unit
val process : EcParsetree.global -> unit
