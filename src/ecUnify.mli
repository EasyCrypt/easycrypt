(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
open EcUid
open EcSymbols
open EcPath
open EcTypes
open EcDecl

(* -------------------------------------------------------------------- *)
exception UnificationFailure of [`TyUni of ty * ty | `TcCtt of ty * Sp.t]
exception UninstanciateUni

type unienv

type tvar_inst =
| TVIunamed of ty list
| TVInamed  of (EcSymbols.symbol * ty) list

type tvi = tvar_inst option
type uidmap = uid -> ty option

module UniEnv : sig
  val create     : (EcIdent.t * Sp.t) list option -> unienv
  val copy       : unienv -> unienv                 (* constant time *)
  val restore    : dst:unienv -> src:unienv -> unit (* constant time *)
  val fresh      : ?tc:EcPath.Sp.t -> ?ty:ty -> unienv -> ty
  val getnamed   : unienv -> symbol -> EcIdent.t
  val repr       : unienv -> ty -> ty
  val opentvi    : unienv -> ty_params -> tvi -> ty EcIdent.Mid.t
  val openty     : unienv -> ty_params -> tvi -> ty -> ty * ty list
  val opentys    : unienv -> ty_params -> tvi -> ty list -> ty list * ty list
  val closed     : unienv -> bool
  val close      : unienv -> uidmap
  val assubst    : unienv -> uidmap
  val tparams    : unienv -> ty_params
end

val unify : EcEnv.env -> unienv -> ty -> ty -> unit
val hastc : EcEnv.env -> unienv -> ty -> Sp.t -> unit

val tfun_expected : unienv -> EcTypes.ty list -> EcTypes.ty

val select_op :
     ?filter:(operator -> bool) -> tvi -> EcEnv.env -> qsymbol -> unienv
  -> dom -> ((EcPath.path * ty list) * ty * unienv) list
