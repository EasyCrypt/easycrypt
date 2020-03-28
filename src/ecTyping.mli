(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcEnv
open EcDecl
open EcPath
open EcLocation
open EcParsetree
open EcTypes
open EcModules

(* -------------------------------------------------------------------- *)
type opmatch = [
  | `Op   of EcPath.path * EcTypes.ty list
  | `Lc   of EcIdent.t
  | `Var  of EcTypes.prog_var
  | `Proj of EcTypes.prog_var * EcTypes.ty * (int * int)
]

type mismatch_funsig =
| MF_targs of ty * ty (* expected, got *)
| MF_tres  of ty * ty (* expected, got *)
| MF_restr of EcEnv.env * [`Eq of Sx.t * Sx.t | `Sub of Sx.t ]

type tymod_cnv_failure =
| E_TyModCnv_ParamCountMismatch
| E_TyModCnv_ParamTypeMismatch of EcIdent.t
| E_TyModCnv_MissingComp       of symbol
| E_TyModCnv_MismatchFunSig    of symbol * mismatch_funsig
| E_TyModCnv_SubTypeArg        of
    EcIdent.t * module_type * module_type * tymod_cnv_failure

type modapp_error =
| MAE_WrongArgCount      of int * int  (* expected, got *)
| MAE_InvalidArgType     of EcPath.mpath * tymod_cnv_failure
| MAE_AccesSubModFunctor

type modtyp_error =
| MTE_IncludeFunctor
| MTE_InnerFunctor
| MTE_DupProcName of symbol

type modsig_error =
| MTS_DupProcName of symbol
| MTS_DupArgName  of symbol * symbol

type funapp_error =
| FAE_WrongArgCount

type mem_error =
| MAE_IsConcrete

type filter_error =
| FE_InvalidIndex of int
| FE_NoMatch

type tyerror =
| UniVarNotAllowed
| FreeTypeVariables
| TypeVarNotAllowed
| OnlyMonoTypeAllowed    of symbol option
| UnboundTypeParameter   of symbol
| UnknownTypeName        of qsymbol
| UnknownTypeClass       of qsymbol
| UnknownRecFieldName    of qsymbol
| UnknownInstrMetaVar    of symbol
| UnknownMetaVar         of symbol
| UnknownProgVar         of qsymbol * EcMemory.memory
| DuplicatedRecFieldName of symbol
| MissingRecField        of symbol
| MixingRecFields        of EcPath.path tuple2
| UnknownProj            of qsymbol
| AmbiguousProj          of qsymbol
| AmbiguousProji         of int * ty
| InvalidTypeAppl        of qsymbol * int * int
| DuplicatedTyVar
| DuplicatedLocal        of symbol
| DuplicatedField        of symbol
| NonLinearPattern
| LvNonLinear
| NonUnitFunWithoutReturn
| TypeMismatch           of (ty * ty) * (ty * ty)
| TypeClassMismatch
| TypeModMismatch        of mpath * module_type * tymod_cnv_failure
| NotAFunction
| AbbrevLowArgs
| UnknownVarOrOp         of qsymbol * ty list
| MultipleOpMatch        of qsymbol * ty list * (opmatch * EcUnify.unienv) list
| UnknownModName         of qsymbol
| UnknownTyModName       of qsymbol
| UnknownFunName         of qsymbol
| UnknownModVar          of qsymbol
| UnknownMemName         of symbol
| InvalidFunAppl         of funapp_error
| InvalidModAppl         of modapp_error
| InvalidModType         of modtyp_error
| InvalidModSig          of modsig_error
| InvalidMem             of symbol * mem_error
| InvalidFilter          of filter_error
| FunNotInModParam       of qsymbol
| NoActiveMemory
| PatternNotAllowed
| MemNotAllowed
| UnknownScope           of qsymbol
| FilterMatchFailure
| LvMapOnNonAssign

exception TymodCnvFailure of tymod_cnv_failure
exception TyError of EcLocation.t * env * tyerror

val tyerror : EcLocation.t -> env -> tyerror -> 'a

(* -------------------------------------------------------------------- *)
val unify_or_fail : env -> EcUnify.unienv -> EcLocation.t -> expct:ty -> ty -> unit

(* -------------------------------------------------------------------- *)
type typolicy

val tp_tydecl : typolicy
val tp_relax  : typolicy

(* -------------------------------------------------------------------- *)
val transtyvars:
  env -> (EcLocation.t * ptyparams option) -> EcUnify.unienv

(* -------------------------------------------------------------------- *)
val transty : typolicy -> env -> EcUnify.unienv -> pty -> ty

val transtys :
    typolicy -> env -> EcUnify.unienv -> pty list -> ty list

val transtvi : env -> EcUnify.unienv -> ptyannot -> EcUnify.tvar_inst

(* -------------------------------------------------------------------- *)
val trans_binding : env -> EcUnify.unienv -> ptybindings ->
  env * (EcIdent.t * EcTypes.ty) list

val trans_gbinding : env -> EcUnify.unienv -> pgtybindings ->
  env * (EcIdent.t * EcFol.gty) list

(* -------------------------------------------------------------------- *)
val transexp :
  env -> [`InProc|`InOp] -> EcUnify.unienv -> pexpr -> expr * ty

val transexpcast :
  env -> [`InProc|`InOp] -> EcUnify.unienv -> ty -> pexpr -> expr

val transexpcast_opt :
  env -> [`InProc|`InOp] -> EcUnify.unienv -> ty option -> pexpr -> expr

(* -------------------------------------------------------------------- *)
type ismap = (instr list) EcMaps.Mstr.t

val transstmt : ?map:ismap -> env -> EcUnify.unienv -> pstmt -> stmt

(* -------------------------------------------------------------------- *)
type ptnmap = ty EcIdent.Mid.t ref
type metavs = EcFol.form Msym.t

val transmem       : env -> EcSymbols.symbol located -> EcIdent.t
val trans_form_opt : env -> ?mv:metavs -> EcUnify.unienv -> pformula -> ty option -> EcFol.form
val trans_form     : env -> ?mv:metavs -> EcUnify.unienv -> pformula -> ty -> EcFol.form
val trans_prop     : env -> ?mv:metavs -> EcUnify.unienv -> pformula -> EcFol.form
val trans_pattern  : env -> ptnmap -> EcUnify.unienv -> pformula -> EcFol.form

(* -------------------------------------------------------------------- *)
val transmodsig  : env -> symbol -> pmodule_sig  -> module_sig
val transmodtype : env -> pmodule_type -> module_type * module_sig
val transmod     : attop:bool -> env -> pmodule_def -> module_expr

val trans_topmsymbol : env -> pmsymbol located -> mpath
val trans_msymbol    : env -> pmsymbol located -> mpath * module_sig
val trans_gamepath   : env -> pgamepath -> xpath

(* -------------------------------------------------------------------- *)
type restriction_who =
| RW_mod of EcPath.mpath
| RW_fun of EcPath.xpath

type restriction_err =
| RE_UseVariable          of EcPath.xpath
| RE_UseVariableViaModule of EcPath.xpath * EcPath.mpath
| RE_UseModule            of EcPath.mpath
| RE_VMissingRestriction  of EcPath.xpath * EcPath.mpath pair
| RE_MMissingRestriction  of EcPath.mpath * EcPath.mpath pair

type restriction_error = restriction_who * restriction_err

exception RestrictionError of EcEnv.env * restriction_error

val check_sig_mt_cnv :
  env -> module_sig -> module_type -> unit

val check_restrictions_fun :
  env -> xpath -> use -> mod_restr -> unit

val check_modtype_with_restrictions :
  env -> mpath -> module_sig -> module_type -> mod_restr -> unit

(* -------------------------------------------------------------------- *)
val get_ring  : (ty_params * ty) -> env -> EcDecl.ring  option
val get_field : (ty_params * ty) -> env -> EcDecl.field option
