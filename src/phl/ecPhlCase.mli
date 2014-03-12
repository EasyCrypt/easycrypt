(* -------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_case   : form -> backward
val t_bdhoare_case : form -> backward
val t_equiv_case   : form -> backward

val t_hl_case : form -> backward
