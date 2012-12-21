(* -------------------------------------------------------------------- *)
open EcUidgen
open EcTypes

(* -------------------------------------------------------------------- *)
exception UnificationFailure of ty * ty

type unienv

module UniEnv : sig
  val create     : unit -> unienv
  val copy       : unienv -> unienv                 (* constant time *)
  val restore    : dst:unienv -> src:unienv -> unit (* constant time *)
  val fresh_uid  : unienv -> ty
  val get_var    : ?strict:bool -> unienv -> string -> EcIdent.t 
  val bind       : unienv -> uid -> ty -> unit
  val repr       : unienv -> ty -> ty
  val dump       : EcDebug.ppdebug -> unienv -> unit
  val freshen    : unienv -> EcIdent.t list -> ty -> unienv * ty
  val freshendom : unienv -> EcIdent.t list -> dom -> unienv * dom
  val freshensig : unienv -> EcIdent.t list -> tysig -> unienv * tysig
  val close      : unienv -> ty Muid.t
  val asmap      : unienv -> ty Muid.t
end

val unify : EcEnv.env -> unienv -> ty -> ty -> unit
