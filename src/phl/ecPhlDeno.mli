(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcCoreGoal.FApi
open EcAst

(* -------------------------------------------------------------------- *)
val t_phoare_deno : ss_inv -> ss_inv -> backward
val t_equiv_deno  : form -> form -> backward

(* -------------------------------------------------------------------- *)
type denoff = deno_ppterm * bool * pformula option

val process_deno : [`PHoare | `EHoare | `Equiv] -> denoff -> backward
