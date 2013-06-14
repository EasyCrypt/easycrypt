(* -------------------------------------------------------------------- *)
open EcSymbols

(* -------------------------------------------------------------------- *)
val process_tactics :
     EcHiLogic.pprovers
  -> EcEnv.env
  -> EcParsetree.ptactic list
  -> EcLogic.goals
  -> EcLogic.goals
