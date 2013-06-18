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
type hitenv = {
  hte_provers : EcParsetree.pprover_infos -> EcProvers.prover_infos;
  hte_smtmode : [`Admit | `Strict | `Standard];
}

(* -------------------------------------------------------------------- *)
val process_form    : EcEnv.LDecl.hyps -> pformula -> ty -> form
val process_formula : goal -> pformula -> form

val process_mkn_apply :
     (goal -> 'a -> form)
  -> 'a fpattern
  -> goal
  -> goal * int list

(* -------------------------------------------------------------------- *)
val process_logic   : hitenv -> EcLocation.t -> logtactic -> goal -> goals
val process_intros  : intropattern -> goal -> goals
val process_trivial : goal -> goals
