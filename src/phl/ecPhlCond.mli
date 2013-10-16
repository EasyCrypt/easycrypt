(* -------------------------------------------------------------------- *)
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
val t_hoare_cond   : tactic
val t_bdHoare_cond : tactic
val t_equiv_cond   : bool option -> tactic

(* -------------------------------------------------------------------- *)
val process_cond : bool option -> tactic
