(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_app   : codepos1 -> form -> backward
val t_bdhoare_app : codepos1 -> form tuple6 -> backward
val t_equiv_app   : codepos1 pair -> form -> backward
val t_equiv_app_onesided : side -> codepos1 -> form -> form -> backward

(* -------------------------------------------------------------------- *)
val process_app : app_info -> backward
