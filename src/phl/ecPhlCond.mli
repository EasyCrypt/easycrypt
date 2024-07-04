(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_cond   : backward
val t_ehoare_cond  : backward
val t_bdhoare_cond : backward
val t_equiv_cond   : oside -> backward

(* -------------------------------------------------------------------- *)
val t_hoare_match   : backward
val t_bdhoare_match : backward
val t_equiv_match   : matchmode -> backward
