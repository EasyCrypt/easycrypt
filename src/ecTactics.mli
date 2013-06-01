(* -------------------------------------------------------------------- *)
open EcSymbols

(* -------------------------------------------------------------------- *)
type tac_error =
  | UnknownHypSymbol of symbol
  | UnknownAxiom     of qsymbol
  | UnknownOperator  of qsymbol
  | BadTyinstance
  | NothingToIntro
  | FormulaExpected
  | MemoryExpected
  | UnderscoreExpected
  | ModuleExpected
  | ElimDoNotWhatToDo
  | NoCurrentGoal

exception TacError of tac_error

val error : EcLocation.t -> tac_error -> 'a

(* -------------------------------------------------------------------- *)
type pprovers = EcParsetree.pprover_infos -> EcProvers.prover_infos

(* -------------------------------------------------------------------- *)
val process_logic_tacs :
     pprovers
  -> EcEnv.env
  -> EcParsetree.ptactics
  -> EcBaseLogic.goals
  -> EcBaseLogic.goals
