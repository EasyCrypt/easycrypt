(* -------------------------------------------------------------------- *)
open EcUid
open EcIdent
open EcPath
open EcSymbols
open EcMaps
open EcTypes
open EcDecl

(* ==================================================================== *)
type problem = [
  | `TyUni of ty * ty
  | `TcTw  of tcwitness * tcwitness
  | `TcCtt of EcUid.uid * ty * typeclass
]

exception UnificationFailure of problem
exception UninstanciateUni

type unienv

type petyarg = ty option * tcwitness option list option

type tvar_inst =
| TVIunamed of petyarg list
| TVInamed  of (EcSymbols.symbol * petyarg) list

type tvi = tvar_inst option

val tvi_unamed : etyarg list -> tvar_inst

module UniEnv : sig
  type opened = {
    subst  : etyarg Mid.t;
    params : (ty * typeclass list) list;
    args   : etyarg list;
  }

  val create     : (EcIdent.t * typeclass list) list option -> unienv
  val copy       : unienv -> unienv                 (* constant time *)
  val restore    : dst:unienv -> src:unienv -> unit (* constant time *)
  val xfresh     : ?tcs:(EcDecl.typeclass * EcTypes.tcwitness option) list -> ?ty:ty -> unienv -> etyarg
  val fresh      : ?ty:ty -> unienv -> ty
  val getnamed   : unienv -> symbol -> EcIdent.t
  val repr       : unienv -> ty -> ty
  val opentvi    : unienv -> ty_params -> tvi -> opened
  val openty     : unienv -> ty_params -> tvi -> ty -> ty * opened 
  val opentys    : unienv -> ty_params -> tvi -> ty list -> ty list * opened
  val closed     : unienv -> bool
  val close      : unienv -> etyarg Muid.t
  val assubst    : unienv -> etyarg Muid.t
  val tparams    : unienv -> ty_params
end

val unify : EcEnv.env -> unienv -> ty -> ty -> unit

val hastc : EcEnv.env -> unienv -> ty -> typeclass -> ((path * ty list) Mstr.t) option option

val tfun_expected : unienv -> EcTypes.ty list -> EcTypes.ty

type sbody = ((EcIdent.t * ty) list * expr) Lazy.t

val select_op :
     ?hidden:bool
  -> ?filter:(EcPath.path -> operator -> bool)
  -> tvi
  -> EcEnv.env
  -> qsymbol
  -> unienv
  -> dom
  -> ((EcPath.path * etyarg list) * ty * unienv * sbody option) list
