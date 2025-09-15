(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* -------------------------------------------------------------------- *)
val t_hoare_app   : codepos1 -> ss_inv -> backward
val t_ehoare_app  : codepos1 -> ss_inv -> backward
val t_bdhoare_app : codepos1 -> ss_inv tuple6 -> backward
val t_equiv_app   : codepos1 pair -> ts_inv -> backward
val t_equiv_app_onesided : side -> codepos1 -> ss_inv -> ss_inv -> backward

(* -------------------------------------------------------------------- *)
val process_app : app_info -> backward
