(* -------------------------------------------------------------------- *)
open EcSymbols

(* -------------------------------------------------------------------- *)
val process_tactics :
     EcHiLogic.pprovers
  -> EcParsetree.ptactic list
  -> EcLogic.goals
  -> EcLogic.goals
