(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_cond   : backward
val t_bdhoare_cond : backward
val t_equiv_cond   : bool option -> backward

(* -------------------------------------------------------------------- *)
val process_cond : bool option -> backward
