(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* FIXME: add t_low* to all these tactics                               *)

(* -------------------------------------------------------------------- *)
val t_equivF_conseq      : form -> form -> FApi.backward
val t_equivS_conseq      : form -> form -> FApi.backward
val t_eagerF_conseq      : form -> form -> FApi.backward
val t_hoareF_conseq      : form -> form -> FApi.backward
val t_hoareS_conseq      : form -> form -> FApi.backward
val t_bdHoareF_conseq    : form -> form -> FApi.backward
val t_bdHoareS_conseq    : form -> form -> FApi.backward
val t_bdHoareS_conseq_bd : hoarecmp -> form -> FApi.backward
val t_bdHoareF_conseq_bd : hoarecmp -> form -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_equivF_conseq_nm   : form -> form -> FApi.backward
val t_equivS_conseq_nm   : form -> form -> FApi.backward
val t_hoareF_conseq_nm   : form -> form -> FApi.backward
val t_hoareS_conseq_nm   : form -> form -> FApi.backward
val t_bdHoareF_conseq_nm : form -> form -> FApi.backward
val t_bdHoareS_conseq_nm : form -> form -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_conseq : form -> form -> FApi.backward

(* -------------------------------------------------------------------- *)
val process_conseq   : bool -> ccfpattern option tuple3 -> FApi.backward
val process_bd_equiv : bool -> pformula pair -> FApi.backward
