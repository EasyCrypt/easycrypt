(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_sp : (codepos1 doption) option -> backward

(* -------------------------------------------------------------------- *)
val process_sp : (pcodepos1 doption) option -> backward
