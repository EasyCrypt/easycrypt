(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hr_exists_elim  : backward
val t_hr_exists_intro : form list -> backward

(* -------------------------------------------------------------------- *)
val process_exists_intro : pformula list -> backward
