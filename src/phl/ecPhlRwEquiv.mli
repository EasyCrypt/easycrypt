(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst
open EcParsetree
open EcCoreGoal
open EcMatching.Position

(* -------------------------------------------------------------------- *)
val t_rewrite_equiv :
  side ->
  [`LtoR | `RtoL ] ->
  pcodepos1 ->
  equivF ->
  proofterm ->
  (expr list * lvalue option) option ->
  backward

val process_rewrite_equiv : rw_eqv_info -> backward
