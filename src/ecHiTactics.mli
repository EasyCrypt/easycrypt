(* -------------------------------------------------------------------- *)
open EcSymbols

(* -------------------------------------------------------------------- *)
val process_tactics :
     EcHiLogic.pprovers
  -> EcEnv.env
  -> EcParsetree.ptactic list
  -> EcBaseLogic.goals
  -> EcBaseLogic.goals
