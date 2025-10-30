(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcAst

(* -------------------------------------------------------------------- *)
val t_hoare_while      : ss_inv -> backward
val t_bdhoare_while    : ss_inv -> ss_inv -> backward
val t_equiv_while_disj : side -> ts_inv -> ts_inv -> backward
val t_equiv_while      : ts_inv -> backward

(* -------------------------------------------------------------------- *)
val process_while : oside -> while_info -> backward
val process_async_while : async_while_info -> backward
