(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* -------------------------------------------------------------------- *)
val t_hoare_case   : ?simplify:bool -> ss_inv -> backward
val t_bdhoare_case : ?simplify:bool -> ss_inv -> backward
val t_equiv_case   : ?simplify:bool -> ts_inv -> backward

val t_hl_case : ?simplify:bool -> inv -> backward
