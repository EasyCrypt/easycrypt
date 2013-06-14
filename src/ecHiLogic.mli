(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcTypes
open EcFol
open EcLogic
open EcBaseLogic

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
val process_form    : EcEnv.LDecl.hyps -> pformula -> ty -> form
val process_formula : goal -> pformula -> form

val process_mkn_apply :
     (EcEnv.env -> goal -> 'a -> form)
  -> EcEnv.env
  -> 'a fpattern
  -> goal
  -> goal * int list

(* -------------------------------------------------------------------- *)
val process_logic  : pprovers -> EcLocation.t -> EcEnv.env -> logtactic -> goal -> goals
val process_intros : EcEnv.env -> intropattern -> goal -> goals
