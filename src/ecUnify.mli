(* -------------------------------------------------------------------- *)
open EcUid
open EcSymbols
open EcPath
open EcTypes
open EcDecl

(* -------------------------------------------------------------------- *)
exception UnificationFailure of [`TyUni of ty * ty]
exception UninstantiateUni

type unienv

type tvar_inst =
| TVIunamed of ty list
| TVInamed  of (EcSymbols.symbol * ty) list

type tvi = tvar_inst option
type uidmap = uid -> ty option

module UniEnv : sig
  val create     : ty_params option -> unienv
  val copy       : unienv -> unienv                 (* constant time *)
  val restore    : dst:unienv -> src:unienv -> unit (* constant time *)
  val fresh      : ?ty:ty -> unienv -> ty
  val getnamed   : unienv -> symbol -> EcIdent.t
  val repr       : unienv -> ty -> ty
  val opentvi    : unienv -> ty_params -> tvi -> ty EcIdent.Mid.t
  val openty     : unienv -> ty_params -> tvi -> ty -> ty * ty list
  val opentys    : unienv -> ty_params -> tvi -> ty list -> ty list * ty list
  val closed     : unienv -> bool
  val close      : unienv -> ty Muid.t
  val assubst    : unienv -> ty Muid.t
  val tparams    : unienv -> ty_params
end

val unify : EcEnv.env -> unienv -> ty -> ty -> unit

val tfun_expected : unienv -> ?retty:ty -> EcTypes.ty list -> EcTypes.ty

type sbody = ((EcIdent.t * ty) list * expr) Lazy.t

type select_result = (EcPath.path * ty list) * ty * unienv * sbody option

val select_op :
     ?hidden:bool
  -> ?filter:(path -> operator -> bool)
  -> tvi
  -> EcEnv.env
  -> qsymbol
  -> unienv
  -> dom * ty option
  -> select_result list
