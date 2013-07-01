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
val process_form_opt : EcEnv.LDecl.hyps -> pformula -> ty option -> form
val process_form    : EcEnv.LDecl.hyps -> pformula -> ty -> form
val process_formula : EcEnv.LDecl.hyps -> pformula -> form

val process_mkn_apply :
     ('a -> form)
  -> 'a fpattern
  -> goal
  -> goal * int list

(* -------------------------------------------------------------------- *)
type engine = ptactic_core -> tactic

val process_logic   : engine * hitenv -> EcLocation.t -> logtactic -> tactic
val process_intros  : ?cf:bool -> intropattern -> goal -> goals
val process_trivial : tactic
val process_done    : tactic
