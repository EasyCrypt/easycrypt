(* -------------------------------------------------------------------- *)
open EcSymbols
open EcCoreGoal

(* -------------------------------------------------------------------- *)
val t_pr_rewrite_i : symbol *  EcFol.form option -> FApi.backward
val t_pr_rewrite : symbol * EcParsetree.pformula option -> FApi.backward

