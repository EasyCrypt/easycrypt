(* -------------------------------------------------------------------- *)
open EcParsetree
open EcMatching.Position
open EcCoreGoal.FApi
open EcUtils

(* -------------------------------------------------------------------- *)
val t_sp : (codepos1 doption) option -> backward

(* -------------------------------------------------------------------- *)
val process_sp : (pcodepos1 doption) option -> backward
