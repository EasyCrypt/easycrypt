(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* -------------------------------------------------------------------- *)
val t_hoare_seq   : codepos1 -> ss_inv -> backward
val t_ehoare_seq  : codepos1 -> ss_inv -> backward
val t_bdhoare_seq : codepos1 -> ss_inv tuple6 -> backward
val t_equiv_seq   : codepos1 pair -> ts_inv -> backward
val t_equiv_seq_onesided : side -> codepos1 -> ss_inv -> ss_inv -> backward

(* -------------------------------------------------------------------- *)
val process_seq : seq_info -> backward
