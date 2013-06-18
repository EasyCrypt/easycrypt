(* -------------------------------------------------------------------- *)
open EcSymbols

(* -------------------------------------------------------------------- *)
val process_tactics :
     EcHiLogic.hitenv
  -> EcParsetree.ptactic list
  -> EcLogic.goals
  -> EcLogic.goals
