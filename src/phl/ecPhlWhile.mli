(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_while      : form -> backward
val t_bdhoare_while    : form -> form -> backward
val t_equiv_while_disj : bool -> form -> form -> backward
val t_equiv_while      : form -> backward

(* -------------------------------------------------------------------- *)
val process_while :
     bool option
  -> pformula
  -> pformula option
  -> (pformula * pformula) option
  -> backward
