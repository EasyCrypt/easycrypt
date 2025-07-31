(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal.FApi
open EcAst

(* -------------------------------------------------------------------- *)
val t_hoare_ppr   : backward
val t_bdhoare_ppr : backward
val t_equiv_ppr   : ty -> ss_inv -> ss_inv -> backward

(* -------------------------------------------------------------------- *)
val t_prbounded : bool -> backward
val t_prfalse   : backward

(* -------------------------------------------------------------------- *)
val process_ppr : (pformula tuple2) option -> backward
