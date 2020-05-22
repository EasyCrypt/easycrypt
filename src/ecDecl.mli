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
open EcBigInt
open EcPath
open EcTypes
open EcCoreFol

(* -------------------------------------------------------------------- *)
type ty_param  = EcIdent.t * EcPath.Sp.t
type ty_params = ty_param list
type ty_pctor  = [ `Int of int | `Named of ty_params ]

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

val abs_tydecl : ?tc:Sp.t -> ?params:ty_pctor -> unit -> tydecl

val ty_instanciate : ty_params -> ty list -> ty -> ty

(* -------------------------------------------------------------------- *)
type locals = EcIdent.t list

type operator_kind =
  | OB_oper of opbody option
  | OB_pred of prbody option
  | OB_nott of notation

and opbody =
  | OP_Plain  of EcTypes.expr * bool (* nosmt? *)
  | OP_Constr of EcPath.path * int
  | OP_Record of EcPath.path
  | OP_Proj   of EcPath.path * int * int
  | OP_Fix    of opfix
  | OP_TC

and prbody =
  | PR_Plain of form
  | PR_Ind   of prind

and opfix = {
  opf_args     : (EcIdent.t * EcTypes.ty) list;
  opf_resty    : EcTypes.ty;
  opf_struct   : int list * int;
  opf_branches : opbranches;
  opf_nosmt    : bool;
}

and opbranches =
| OPB_Leaf   of ((EcIdent.t * EcTypes.ty) list) list * EcTypes.expr
| OPB_Branch of opbranch Parray.parray

and opbranch = {
  opb_ctor : EcPath.path * int;
  opb_sub  : opbranches;
}

and notation = {
  ont_args  : (EcIdent.t * EcTypes.ty) list;
  ont_resty : EcTypes.ty;
  ont_body  : expr;
  ont_ponly : bool;
}

and prind = {
  pri_args  : (EcIdent.t * EcTypes.ty) list;
  pri_ctors : prctor list;
}

and prctor = {
  prc_ctor : symbol;
  prc_bds  : (EcIdent.t * gty) list;
  prc_spec : form list;
}

type operator = {
  op_tparams : ty_params;
  op_ty      : EcTypes.ty;
  op_kind    : operator_kind;
}

val op_ty     : operator -> ty
val is_pred   : operator -> bool
val is_oper   : operator -> bool
val is_ctor   : operator -> bool
val is_proj   : operator -> bool
val is_rcrd   : operator -> bool
val is_fix    : operator -> bool
val is_abbrev : operator -> bool
val is_prind  : operator -> bool

val mk_op   : ty_params -> ty -> opbody option -> operator
val mk_pred : ty_params -> ty list -> prbody option -> operator

val mk_abbrev :
     ?ponly:bool -> ty_params -> (EcIdent.ident * ty) list
  -> ty * expr -> operator

val operator_as_ctor  : operator -> EcPath.path * int
val operator_as_rcrd  : operator -> EcPath.path
val operator_as_proj  : operator -> EcPath.path * int * int
val operator_as_fix   : operator -> opfix
val operator_as_prind : operator -> prind

(* -------------------------------------------------------------------- *)
type axiom_kind = [`Axiom of (Ssym.t * bool) | `Lemma]

type axiom = {
  ax_tparams : ty_params;
  ax_spec    : form;
  ax_kind    : axiom_kind;
  ax_nosmt   : bool;
}

(* -------------------------------------------------------------------- *)
val is_axiom : axiom_kind -> bool
val is_lemma : axiom_kind -> bool

(* -------------------------------------------------------------------- *)
val axiomatized_op :
     ?nargs: int
  -> ?nosmt:bool
  -> EcPath.path
  -> (ty_params * expr)
  -> axiom

(* -------------------------------------------------------------------- *)
type typeclass = {
  tc_prt : EcPath.path option;
  tc_ops : (EcIdent.t * EcTypes.ty) list;
  tc_axs : (EcSymbols.symbol * form) list;
}

(* -------------------------------------------------------------------- *)
type rkind = [
  | `Boolean
  | `Integer
  | `Modulus of (zint option) pair
]

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
  r_kind  : rkind;
}

val ring_equal : ring -> ring -> bool

(* -------------------------------------------------------------------- *)
type field = {
  f_ring : ring;
  f_inv  : EcPath.path;
  f_div  : EcPath.path option;
}
val field_equal : field -> field -> bool
