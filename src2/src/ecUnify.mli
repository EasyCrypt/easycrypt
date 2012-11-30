(* -------------------------------------------------------------------- *)
open EcTypes

(* -------------------------------------------------------------------- *)
exception UnificationFailure of ty * ty

val unify : EcEnv.env -> ty EcUidgen.Muid.t -> ty -> ty -> ty EcUidgen.Muid.t
