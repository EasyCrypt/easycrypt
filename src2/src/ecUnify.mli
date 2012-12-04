(* -------------------------------------------------------------------- *)
open EcUidgen
open EcTypes

(* -------------------------------------------------------------------- *)
exception UnificationFailure of ty * ty

type unienv

module UniEnv : sig
  val create  : unit -> unienv
  val copy    : unienv -> unienv                 (* constant time *)
  val restore : dst:unienv -> src:unienv -> unit (* constant time *)
  val asmap   : unienv -> ty Muid.t
  val bind    : unienv -> uid -> ty -> unit
  val repr    : unienv -> ty -> ty
end

val unify : EcEnv.env -> unienv -> ty -> ty -> unit
