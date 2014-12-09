(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils

module Sp = EcPath.Sp
module TC = EcTypeClass

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
  | `Record   of EcCoreFol.form * (EcSymbols.symbol * EcTypes.ty) list
]

and ty_dtype = {
  tydt_ctors   : (EcSymbols.symbol * EcTypes.ty list) list;
  tydt_schelim : EcCoreFol.form;
  tydt_schcase : EcCoreFol.form;
}

let tydecl_as_concrete (td : tydecl) =
  match td.tyd_type with `Concrete x -> x | _ -> assert false

let tydecl_as_abstract (td : tydecl) =
  match td.tyd_type with `Abstract x -> x | _ -> assert false

let tydecl_as_datatype (td : tydecl) =
  match td.tyd_type with `Datatype x -> x | _ -> assert false

let tydecl_as_record (td : tydecl) =
  match td.tyd_type with `Record x -> x | _ -> assert false

(* -------------------------------------------------------------------- *)
type locals = EcIdent.t list 

type operator_kind =
  | OB_oper of opbody option
  | OB_pred of EcCoreFol.form option

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

(* -------------------------------------------------------------------- *)
type axiom_kind = [`Axiom | `Lemma]

type axiom = {
  ax_tparams : ty_params;
  ax_spec    : EcCoreFol.form option;
  ax_kind    : axiom_kind;
  ax_nosmt   : bool;
}

(* -------------------------------------------------------------------- *)
let op_ty op = op.op_ty

let is_oper op = 
  match op.op_kind with
  | OB_oper _ -> true
  | _ -> false

let is_pred op = 
  match op.op_kind with
  | OB_pred _ -> true
  | _ -> false

let is_ctor op =
  match op.op_kind with
  | OB_oper (Some (OP_Constr _)) -> true
  | _ -> false

let is_proj op =
  match op.op_kind with
  | OB_oper (Some (OP_Proj _)) -> true
  | _ -> false
 
let is_rcrd op =
  match op.op_kind with
  | OB_oper (Some (OP_Record _)) -> true
  | _ -> false

let is_fix op =
  match op.op_kind with
  | OB_oper (Some (OP_Fix _)) -> true
  | _ -> false

let gen_op tparams ty kind = {
  op_tparams = tparams;
  op_ty      = ty;
  op_kind    = kind;
}

let mk_pred tparams dom body =
  let kind = OB_pred body in
    gen_op tparams (EcTypes.toarrow dom EcTypes.tbool) kind

let mk_op tparams ty body = 
  let kind = OB_oper body in
    gen_op tparams ty kind

let operator_as_ctor (op : operator) =
  match op.op_kind with
  | OB_oper (Some (OP_Constr (indp, ctor))) -> (indp, ctor)
  | _ -> assert false

let operator_as_proj (op : operator) =
  match op.op_kind with
  | OB_oper (Some (OP_Proj (recp, i1, i2))) -> (recp, i1, i2)
  | _ -> assert false

let operator_as_rcrd (op : operator) =
  match op.op_kind with
  | OB_oper (Some (OP_Record recp)) -> recp
  | _ -> assert false

let operator_as_fix (op : operator) =
  match op.op_kind with
  | OB_oper (Some (OP_Fix fix)) -> fix
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let axiomatized_op ?(nosmt = false) path (tparams, bd) =
  let axbd = EcCoreFol.form_of_expr EcCoreFol.mhr bd in
  let axbd, axpm =
    let bdpm = List.map fst tparams in
    let axpm = List.map EcIdent.fresh bdpm in
      (EcCoreFol.Fsubst.subst_tvar
         (EcTypes.Tvar.init bdpm (List.map EcTypes.tvar axpm))
         axbd,
       List.combine axpm (List.map snd tparams))
  in

  let axspec =
    EcCoreFol.f_eq
      (EcCoreFol.f_op path
         (List.map (EcTypes.tvar |- fst) axpm)
         axbd.EcCoreFol.f_ty)
      axbd
  in

  { ax_tparams = axpm;
    ax_spec    = Some axspec;
    ax_kind    = `Axiom;
    ax_nosmt   = nosmt; }

(* -------------------------------------------------------------------- *)
type typeclass = {
  tc_prt : EcPath.path option;
  tc_ops : (EcIdent.t * EcTypes.ty) list;
  tc_axs : (EcSymbols.symbol * EcCoreFol.form) list;
}

(* -------------------------------------------------------------------- *)
type rkind = [
  | `Boolean
  | `Integer
  | `Modulus of int option * int option
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

let kind_equal k1 k2 =
  match k1, k2 with
  | `Boolean, `Boolean -> true
  | `Integer, `Integer -> true

  | `Modulus (n1, p1), `Modulus (n2, p2) ->
         opt_equal ((==) : int -> int -> bool) n1 n2
      && opt_equal ((==) : int -> int -> bool) p1 p2

  | _, _ -> false

let ring_equal r1 r2 = 
  EcTypes.ty_equal r1.r_type r2.r_type &&
  EcPath.p_equal r1.r_zero r2.r_zero &&
  EcPath.p_equal r1.r_one  r2.r_one  &&
  EcPath.p_equal r1.r_add  r2.r_add  &&
  EcUtils.oall2 EcPath.p_equal r1.r_opp r2.r_opp  &&
  EcPath.p_equal r1.r_mul  r2.r_mul  &&
  EcUtils.oall2 EcPath.p_equal r1.r_exp  r2.r_exp  &&
  EcUtils.oall2 EcPath.p_equal r1.r_sub r2.r_sub &&
  kind_equal r1.r_kind r2.r_kind &&
  match r1.r_embed, r2.r_embed with
  | `Direct, `Direct -> true
  | `Embed p1, `Embed p2 -> EcPath.p_equal p1 p2
  | `Default, `Default -> true
  | _, _ -> false

  
type field = {
  f_ring : ring;
  f_inv  : EcPath.path;
  f_div  : EcPath.path option;
}

let field_equal f1 f2 = 
  ring_equal f1.f_ring f2.f_ring && 
  EcPath.p_equal f1.f_inv f2.f_inv &&
  EcUtils.oall2 EcPath.p_equal f1.f_div f2.f_div
