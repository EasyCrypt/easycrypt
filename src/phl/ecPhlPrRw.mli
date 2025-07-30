(* -------------------------------------------------------------------- *)
open EcSymbols
open EcCoreGoal
open EcAst

(* -------------------------------------------------------------------- *)
val t_pr_rewrite_i : symbol * ss_inv option -> FApi.backward
val t_pr_rewrite : symbol * EcParsetree.pformula option -> FApi.backward

