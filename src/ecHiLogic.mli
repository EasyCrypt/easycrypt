(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcLogic

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
type engine = ptactic_core -> tactic

val process_logic   : engine * hitenv -> EcLocation.t -> logtactic -> tactic
val process_intros  : ?cf:bool -> intropattern -> goal  -> goals
val process_mintros : ?cf:bool -> intropattern -> goals -> goals
val process_trivial : tactic
val process_rewrite : EcLocation.t -> rwarg list -> tactic
val process_done    : tactic
