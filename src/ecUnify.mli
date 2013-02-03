(* -------------------------------------------------------------------- *)
open EcUidgen
open EcTypes

(* -------------------------------------------------------------------- *)
exception TypeVarCycle of uid * ty
exception UnificationFailure of ty * ty
exception DuplicateTvar of EcSymbols.symbol
exception UninstanciateUni of uid

type unienv

module UniEnv : sig
  type tvar_inst_kind = 
    | TVIunamed of ty list
    | TVInamed  of (EcSymbols.symbol * ty) list

  type tvi = tvar_inst_kind option

  val create     : EcIdent.t list option -> unienv
  val copy       : unienv -> unienv                 (* constant time *)
  val restore    : dst:unienv -> src:unienv -> unit (* constant time *)
  val fresh_uid  : unienv -> ty
  val get_var    : unienv -> string -> EcIdent.t 
  val bind       : unienv -> uid -> ty -> unit
  val repr       : unienv -> ty -> ty
  val dump       : EcDebug.ppdebug -> unienv -> unit
  val freshen    : unienv -> EcIdent.t list -> tvi -> ty -> unienv * ty * ty list
  val freshendom : unienv -> EcIdent.t list -> tvi -> dom -> unienv * dom * ty list
  val freshensig : unienv -> EcIdent.t list -> tvi -> tysig -> unienv * tysig * ty list
  val close      : unienv -> ty Muid.t
  val asmap      : unienv -> ty Muid.t
  val tparams    : unienv -> EcIdent.t list
end

val unify : EcEnv.env -> unienv -> ty -> ty -> unit

val filter_tvi : UniEnv.tvi -> EcDecl.operator -> bool

val tfun_expected : unienv -> EcTypes.dom -> EcTypes.ty

val select_op : 
           (* pred allowed *) bool ->
           UniEnv.tvi -> EcEnv.env ->
           EcSymbols.qsymbol -> unienv -> dom ->
           ((EcPath.path * ty list) * ty * unienv) list

