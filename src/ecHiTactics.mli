(* -------------------------------------------------------------------- *)
open EcSymbols

(* -------------------------------------------------------------------- *)
val process_logic_tacs :
     EcHiLogic.pprovers
  -> EcEnv.env
  -> EcParsetree.ptactics
  -> EcBaseLogic.goals
  -> EcBaseLogic.goals
