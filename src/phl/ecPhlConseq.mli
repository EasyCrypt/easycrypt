(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal
open EcAst

(* -------------------------------------------------------------------- *)
(* FIXME: add t_low* to all these tactics                               *)

(* -------------------------------------------------------------------- *)
val t_equivF_conseq       : ts_inv -> ts_inv -> FApi.backward
val t_equivS_conseq       : ts_inv -> ts_inv -> FApi.backward
val t_eagerF_conseq       : ts_inv -> ts_inv -> FApi.backward
val t_hoareF_conseq       : ss_inv -> ss_inv -> FApi.backward
val t_hoareS_conseq       : ss_inv -> ss_inv -> FApi.backward
val t_bdHoareF_conseq     : ss_inv -> ss_inv -> FApi.backward
val t_bdHoareS_conseq     : ss_inv -> ss_inv -> FApi.backward

val t_ehoareF_conseq      : ss_inv -> ss_inv -> FApi.backward
val t_ehoareS_conseq      : ss_inv -> ss_inv -> FApi.backward
val t_bdHoareS_conseq_bd  : hoarecmp -> ss_inv -> FApi.backward
val t_bdHoareF_conseq_bd  : hoarecmp -> ss_inv -> FApi.backward

val t_hoareS_conseq_conj : ss_inv -> ss_inv -> ss_inv -> ss_inv -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_equivF_conseq_nm    : ts_inv -> ts_inv -> FApi.backward
val t_equivS_conseq_nm    : ts_inv -> ts_inv -> FApi.backward
val t_hoareF_conseq_nm    : ss_inv -> ss_inv -> FApi.backward
val t_hoareS_conseq_nm    : ss_inv -> ss_inv -> FApi.backward
val t_bdHoareF_conseq_nm  : ss_inv -> ss_inv -> FApi.backward
val t_bdHoareS_conseq_nm  : ss_inv -> ss_inv -> FApi.backward
(* -------------------------------------------------------------------- *)
val t_ehoareS_concave : ss_inv -> ss_inv -> ss_inv -> FApi.backward
val t_ehoareF_concave : ss_inv -> ss_inv -> ss_inv -> FApi.backward
val t_concave_incr : FApi.backward

(* -------------------------------------------------------------------- *)
val t_equivS_conseq_bd : side -> ss_inv -> ss_inv ->FApi.backward

(* -------------------------------------------------------------------- *)
val t_conseq : inv -> inv -> FApi.backward

(* -------------------------------------------------------------------- *)
val process_conseq   : bool -> conseq_ppterm option tuple3 -> FApi.backward
val process_bd_equiv : side -> pformula pair -> FApi.backward

(* -------------------------------------------------------------------- *)
val process_conseq_opt :
  pcqoptions -> conseq_ppterm option tuple3 -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_conseqauto : ?delta:bool -> ?tsolve:FApi.backward -> FApi.backward

val process_concave : pformula option tuple2 gppterm * pformula -> FApi.backward
