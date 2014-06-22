(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcTypes
open EcFol

(* -------------------------------------------------------------------- *)
type ty_param  = EcIdent.t * EcPath.Sp.t
type ty_params = ty_param list

type tydecl = {
  tyd_params : ty_params;
  tyd_type   : ty_body;
}

and ty_body = [
  | `Concrete of EcTypes.ty
  | `Abstract of Sp.t
  | `Datatype of ty_dtype
  | `Record   of form * (EcSymbols.symbol * EcTypes.ty) list
]

and ty_dtype = {
  tydt_ctors   : (EcSymbols.symbol * EcTypes.ty list) list;
  tydt_schelim : form;
  tydt_schcase : form;
}

val tydecl_as_concrete : tydecl -> EcTypes.ty
val tydecl_as_abstract : tydecl -> Sp.t
val tydecl_as_datatype : tydecl -> ty_dtype
val tydecl_as_record   : tydecl -> form * (EcSymbols.symbol * EcTypes.ty) list

(* -------------------------------------------------------------------- *)
type locals = EcIdent.t list

type operator_kind = 
  | OB_oper of opbody option
  | OB_pred of EcFol.form option

and opbody =
  | OP_Plain  of EcTypes.expr
  | OP_Constr of EcPath.path * int
  | OP_Record of EcPath.path
  | OP_Proj   of EcPath.path * int * int
  | OP_Fix    of opfix
  | OP_TC

and opfix = {
  opf_args     : (EcIdent.t * EcTypes.ty) list;
  opf_resty    : EcTypes.ty;
  opf_struct   : int list * int;
  opf_branches : opbranches;
}

and opbranches =
| OPB_Leaf   of ((EcIdent.t * EcTypes.ty) list) list * EcTypes.expr
| OPB_Branch of opbranch Parray.t

and opbranch = {
  opb_ctor : EcPath.path * int;
  opb_sub  : opbranches;
}

type operator = {
  op_tparams : ty_params;
  op_ty      : EcTypes.ty;        
  op_kind    : operator_kind;
}

val op_ty   : operator -> ty
val is_pred : operator -> bool
val is_oper : operator -> bool
val is_ctor : operator -> bool
val is_proj : operator -> bool
val is_rcrd : operator -> bool
val is_fix  : operator -> bool

val mk_op   : ty_params -> ty -> opbody option -> operator
val mk_pred : ty_params -> ty list -> form option -> operator

val operator_as_ctor : operator -> EcPath.path * int
val operator_as_rcrd : operator -> EcPath.path
val operator_as_proj : operator -> EcPath.path * int * int
val operator_as_fix  : operator -> opfix

(* -------------------------------------------------------------------- *)
type axiom_kind = [`Axiom | `Lemma]

type axiom = {
  ax_tparams : ty_params;
  ax_spec    : EcFol.form option;
  ax_kind    : axiom_kind;
  ax_nosmt   : bool;
}

(* -------------------------------------------------------------------- *)
type typeclass = {
  tc_prt : EcPath.path option;
  tc_ops : (EcIdent.t * EcTypes.ty) list;
  tc_axs : (EcSymbols.symbol * form) list;
}

(* -------------------------------------------------------------------- *)
type ring = {
  r_type  : EcTypes.ty;
  r_zero  : EcPath.path;
  r_one   : EcPath.path;
  r_add   : EcPath.path;
  r_opp   : EcPath.path option;
  r_mul   : EcPath.path;
  r_exp   : EcPath.path option;
  r_sub   : EcPath.path option;
  r_embed : [ `Direct | `Embed of EcPath.path | `Default];
  r_bool  : bool; (* true means boolean ring *)
}

val ring_equal : ring -> ring -> bool

(* -------------------------------------------------------------------- *)
type field = {
  f_ring : ring;
  f_inv  : EcPath.path;
  f_div  : EcPath.path option;
}
val field_equal : field -> field -> bool
