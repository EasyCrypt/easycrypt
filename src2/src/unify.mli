(* -------------------------------------------------------------------- *)
open Types

(* -------------------------------------------------------------------- *)
exception UnificationFailure of ty * ty

val unify : Env.env -> ty UidGen.Muid.t -> ty -> ty -> ty UidGen.Muid.t
