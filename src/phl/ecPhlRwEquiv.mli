open EcCoreGoal.FApi
open EcParsetree
open EcCoreGoal
open EcAst

val t_rewrite_equiv :
  side ->
  [`LtoR | `RtoL ] ->
  codepos1 ->
  equivF ->
  proofterm ->
  (expr list * lvalue option) option ->
  backward

val process_rewrite_equiv : rw_eqv_info -> backward
