(* -------------------------------------------------------------------- *)
open EcUidgen
open EcSymbols
open EcPath
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
  val create     : (EcIdent.t * Sp.t) list option -> unienv
  val copy       : unienv -> unienv                 (* constant time *)
  val restore    : dst:unienv -> src:unienv -> unit (* constant time *)
  val fresh      : ?tc:EcPath.Sp.t -> ?ty:ty -> unienv -> ty
  val getnamed   : unienv -> symbol -> EcIdent.t 
  val repr       : unienv -> ty -> ty
  val opentvi    : unienv -> ty_params -> tvi -> ty EcIdent.Mid.t
  val openty     : unienv -> ty_params -> tvi -> ty -> ty * ty list
  val closed     : unienv -> bool
  val close      : unienv -> (uid -> ty option)
  val assubst    : unienv -> (uid -> ty option)
  val tparams    : unienv -> ty_params
end

val unify : EcEnv.env -> unienv -> ty -> ty -> unit

val tfun_expected : unienv -> EcTypes.ty list -> EcTypes.ty

val select_op : 
     preds:bool -> tvi -> EcEnv.env -> qsymbol -> unienv
  -> dom -> ((EcPath.path * ty list) * ty * unienv) list
