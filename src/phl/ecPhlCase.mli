(* -------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_case   : ?simplify:bool -> form -> backward
val t_choare_case  : ?simplify:bool -> form -> backward
val t_bdhoare_case : ?simplify:bool -> form -> backward
val t_equiv_case   : ?simplify:bool -> form -> backward

val t_hl_case : ?simplify:bool -> form -> backward
