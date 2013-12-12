(* -------------------------------------------------------------------- *)
open EcParsetree
open EcLogic

(* -------------------------------------------------------------------- *)
val process_phl : EcLocation.t -> phltactic -> goal -> goals
