(* -------------------------------------------------------------------- *)
open EcSymbols

(* -------------------------------------------------------------------- *)
val process_logic_tacs :
     EcHiLogic.pprovers
  -> EcEnv.env
  -> EcParsetree.ptactic list
  -> EcBaseLogic.goals
  -> EcBaseLogic.goals
