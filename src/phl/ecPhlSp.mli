(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_sp : (codegap1 doption) option -> backward

(* -------------------------------------------------------------------- *)
val process_sp : (pcodegap1 doption) option -> backward
