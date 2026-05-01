(* -------------------------------------------------------------------- *)
open EcIdent
open EcSymbols
open EcTypes
open EcAst
open EcDecl

(* ==================================================================== *)
type problem = [
  | `TyUni of ty * ty
  | `TcTw  of tcwitness * tcwitness
  | `TcCtt of EcAst.tcuni * ty * typeclass
]

type uniflags = { tyvars: bool; tcvars: bool; }

exception UnificationFailure of problem
exception UninstanciateUni of uniflags

(* Raised by the unifier's By-args strategy when a typeclass with
   ground arguments has multiple matching instances and no further
   unification can disambiguate. The first field is the offending
   typeclass; the second is the list of candidate instance paths. *)
exception AmbiguousTcInstance of typeclass * EcPath.path list

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
  val push       : (EcIdent.t * typeclass list) -> unienv -> unit
  val copy       : unienv -> unienv                 (* constant time *)
  val restore    : dst:unienv -> src:unienv -> unit (* constant time *)
  val xfresh     : ?tcs:(typeclass * EcTypes.tcwitness option) list -> ?ty:ty -> unienv -> etyarg
  val fresh      : ?ty:ty -> unienv -> ty
  val getnamed   : unienv -> symbol -> EcIdent.t
  val repr       : unienv -> ty -> ty
  val opentvi    : unienv -> ty_params -> tvi -> opened
  val openty     : unienv -> ty_params -> tvi -> ty -> ty * opened 
  val opentys    : unienv -> ty_params -> tvi -> ty list -> ty list * opened
  val closed     : unienv -> bool
  val xclosed    : unienv -> uniflags option
  val close      : unienv -> ty TyUni.Muid.t
  val assubst    : unienv -> ty TyUni.Muid.t
  val tparams    : unienv -> ty_params
end

val unify        : EcEnv.env -> unienv -> ty -> ty -> unit
val unify_tcw    : EcEnv.env -> unienv -> tcwitness -> tcwitness -> unit
val unify_etyarg : EcEnv.env -> unienv -> etyarg -> etyarg -> unit

val tfun_expected : unienv -> ?retty:ty -> EcTypes.ty list -> EcTypes.ty

type sbody = ((EcIdent.t * ty) list * expr) Lazy.t

val select_op :
     ?hidden:bool
  -> ?filter:(EcPath.path -> operator -> bool)
  -> ?retty:ty
  -> tvi
  -> EcEnv.env
  -> qsymbol
  -> unienv
  -> dom
  -> ((EcPath.path * etyarg list) * ty * unienv * sbody option) list
