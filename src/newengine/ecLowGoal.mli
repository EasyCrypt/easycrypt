(* -------------------------------------------------------------------- *)
open EcLocation
open EcIdent
open EcCoreGoal

(* -------------------------------------------------------------------- *)
val t_admit   : FApi.backward
val t_apply   : proofterm -> FApi.backward
val t_rewrite : proofterm -> EcMatching.ptnpos -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_intros  : ident mloc list -> FApi.backward
val t_intro_i : ident -> FApi.backward
