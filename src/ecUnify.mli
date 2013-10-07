(* -------------------------------------------------------------------- *)
open EcUidgen
open EcSymbols
open EcTypes
open EcDecl

(* -------------------------------------------------------------------- *)
exception UnificationFailure of ty * ty
exception UninstanciateUni

type unienv

type tvar_inst =
| TVIunamed of ty list
| TVInamed  of (EcSymbols.symbol * ty) list

type tvi = tvar_inst option

module UniEnv : sig
  val create     : EcIdent.t list option -> unienv
  val copy       : unienv -> unienv                 (* constant time *)
  val restore    : dst:unienv -> src:unienv -> unit (* constant time *)
  val fresh      : unienv -> ty
  val getnamed   : unienv -> symbol -> EcIdent.t 
  val repr       : unienv -> ty -> ty
  val freshen_ue : unienv -> ty_params -> tvi -> ty EcIdent.Mid.t
  val freshen    : unienv -> ty_params -> tvi -> ty -> unienv * ty * ty list
  val closed     : unienv -> bool
  val close      : unienv -> (uid -> ty option)
  val assubst    : unienv -> (uid -> ty option)
  val tparams    : unienv -> ty_params
end

val unify : EcEnv.env -> unienv -> ty -> ty -> unit

val filter_tvi : tvi -> EcDecl.operator -> bool

val tfun_expected : unienv -> EcTypes.ty list -> EcTypes.ty

val select_op : 
  (* pred allowed *) bool ->
  tvi -> EcEnv.env ->
  EcSymbols.qsymbol -> unienv -> dom ->
  ((EcPath.path * ty list) * ty * unienv) list
