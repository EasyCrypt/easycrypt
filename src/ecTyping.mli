(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcLocation
open EcParsetree
open EcTypes
open EcDecl
open EcModules

(* -------------------------------------------------------------------- *)
type modapp_error =
| MAE_WrongArgPosition
| MAE_WrongArgCount
| MAE_InvalidArgType
| MAE_AccesSubModFunctor

type modtyp_error =
| MTE_FunSigDoesNotRepeatArgNames

type funapp_error =
| FAE_WrongArgCount

type mem_error =
| MAE_IsConcrete

type tyerror =
| UniVarNotAllowed
| TypeVarNotAllowed
| OnlyMonoTypeAllowed
| UnboundTypeParameter of symbol
| UnknownTypeName      of qsymbol
| InvalidTypeAppl      of qsymbol * int * int
| DuplicatedTyVar
| DuplicatedLocal      of symbol
| NonLinearPattern
| TypeMismatch         of (ty * ty) * (ty * ty)
| UnknownVarOrOp       of qsymbol * ty list
| MultipleOpMatch      of qsymbol * ty list
| UnknownModName       of qsymbol
| UnknownTyModName     of qsymbol
| UnknownFunName       of qsymbol
| UnknownModVar        of qsymbol
| UnknownMemName       of int * symbol
| InvalidFunAppl       of funapp_error
| InvalidModAppl       of modapp_error
| InvalidModType       of modtyp_error
| InvalidMem           of symbol * mem_error
| OnlyModParamAreOracle of qsymbol
| LvTupleNotUniq

exception TyError of EcLocation.t * EcEnv.env * tyerror

val tyerror : EcLocation.t -> EcEnv.env -> tyerror -> 'a

(* -------------------------------------------------------------------- *)
type typolicy

val tp_tydecl : typolicy
val tp_relax  : typolicy

(* -------------------------------------------------------------------- *)
val ue_for_decl :
     EcEnv.env
  -> (EcLocation.t * psymbol list option)
  -> EcUnify.unienv

(* -------------------------------------------------------------------- *)
val transty : typolicy -> EcEnv.env -> EcUnify.unienv -> pty -> ty 

val transtys :  
    typolicy -> EcEnv.env -> EcUnify.unienv -> pty list -> ty list

val transtvi : EcEnv.env -> EcUnify.unienv -> ptyannot -> EcUnify.UniEnv.tvar_inst_kind

val transbinding :  EcEnv.env -> EcUnify.unienv -> ptybindings ->
  EcEnv.env * (EcIdent.t * EcTypes.ty) list

(* -------------------------------------------------------------------- *)
val transexp : EcEnv.env -> EcUnify.unienv -> pexpr -> expr * ty
val transexpcast : EcEnv.env -> EcUnify.unienv -> ty -> pexpr -> expr

(* -------------------------------------------------------------------- *)
val transmem     : EcEnv.env -> EcSymbols.symbol located -> EcIdent.t
val transformula : EcEnv.env -> EcUnify.unienv -> pformula -> EcFol.form 
val transform    : EcEnv.env -> EcUnify.unienv -> pformula -> ty -> EcFol.form
val transform_opt: EcEnv.env -> EcUnify.unienv -> pformula -> ty option -> EcFol.form

(* -------------------------------------------------------------------- *)
val transmodsig   : EcEnv.env -> symbol -> pmodule_sig  -> module_sig
val transmodtype  : EcEnv.env -> pmodule_type -> module_type * module_sig
val transmod      : EcEnv.env -> symbol -> pmodule_expr -> module_expr
val trans_msymbol : EcEnv.env -> pmsymbol located -> mpath * module_sig
val trans_gamepath : EcEnv.env -> pgamepath -> xpath 
(* -------------------------------------------------------------------- *)

val check_sig_mt_cnv : EcEnv.env -> module_sig -> module_type -> unit 
