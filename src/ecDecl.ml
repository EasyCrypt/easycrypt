(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcCoreFol

module Sp   = EcPath.Sp
module TC   = EcTypeClass
module BI   = EcBigInt
module Ssym = EcSymbols.Ssym

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
let abs_tydecl ?(tc = Sp.empty) ?(params = `Int 0) () =
  let params =
    match params with
    | `Named params ->
        params
    | `Int n ->
        let fmt = fun x -> Printf.sprintf "'%s" x in
        List.map
          (fun x -> (EcIdent.create x, Sp.empty))
          (EcUid.NameGen.bulk ~fmt n)
  in

  { tyd_params = params; tyd_type = `Abstract tc; }

(* -------------------------------------------------------------------- *)
let ty_instanciate (params : ty_params) (args : ty list) (ty : ty) =
  let subst = EcTypes.Tvar.init (List.map fst params) args in
  EcTypes.Tvar.subst subst ty

(* -------------------------------------------------------------------- *)
type locals = EcIdent.t list

type operator_kind =
  | OB_oper of opbody option
  | OB_pred of prbody option
  | OB_nott of notation

and opbody =
  | OP_Plain  of EcTypes.expr * bool  (* nosmt? *)
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
  prc_ctor : EcSymbols.symbol;
  prc_bds  : (EcIdent.t * gty) list;
  prc_spec : form list;
}

type operator = {
  op_tparams : ty_params;
  op_ty      : EcTypes.ty;
  op_kind    : operator_kind;
}

(* -------------------------------------------------------------------- *)
type axiom_kind = [`Axiom of (Ssym.t * bool) | `Lemma]

type axiom = {
  ax_tparams : ty_params;
  ax_spec    : EcCoreFol.form;
  ax_kind    : axiom_kind;
  ax_nosmt   : bool; }

let is_axiom (x : axiom_kind) = match x with `Axiom _ -> true | _ -> false
let is_lemma (x : axiom_kind) = match x with `Lemma   -> true | _ -> false

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

let is_abbrev op =
  match op.op_kind with
  | OB_nott _ -> true
  | _ -> false

let is_prind op =
  match op.op_kind with
  | OB_pred (Some (PR_Ind _)) -> true
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

let mk_abbrev ?(ponly = false) tparams xs (codom, body) =
  let kind = {
    ont_args  = xs;
    ont_resty = codom;
    ont_body  = body;
    ont_ponly = ponly;
  } in

  gen_op tparams (EcTypes.toarrow (List.map snd xs) codom) (OB_nott kind)

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

let operator_as_prind (op : operator) =
  match op.op_kind with
  | OB_pred (Some (PR_Ind pri)) -> pri
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let axiomatized_op ?(nargs = 0) ?(nosmt = false) path (tparams, bd) =
  let axbd = EcCoreFol.form_of_expr EcCoreFol.mhr bd in
  let axbd, axpm =
    let bdpm = List.map fst tparams in
    let axpm = List.map EcIdent.fresh bdpm in
      (EcCoreFol.Fsubst.subst_tvar
         (EcTypes.Tvar.init bdpm (List.map EcTypes.tvar axpm))
         axbd,
       List.combine axpm (List.map snd tparams))
  in

  let args, axbd =
    match axbd.f_node with
    | Fquant (Llambda, bds, axbd) ->
        let bds, flam = List.split_at nargs bds in
        (bds, f_lambda flam axbd)
    | _ -> [], axbd
  in

  let opargs = List.map (fun (x, ty) -> f_local x (gty_as_ty ty)) args in
  let tyargs = List.map (EcTypes.tvar |- fst) axpm in
  let op     = f_op path tyargs (toarrow (List.map f_ty opargs) axbd.EcCoreFol.f_ty) in
  let op     = f_app op opargs axbd.f_ty in
  let axspec = f_forall args (f_eq op axbd) in

  { ax_tparams = axpm;
    ax_spec    = axspec;
    ax_kind    = `Axiom (Ssym.empty, false);
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
  | `Modulus of (BI.zint option) pair
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
         opt_equal BI.equal n1 n2
      && opt_equal BI.equal p1 p2

  | _, _ -> false

let ring_equal r1 r2 =
     EcTypes.ty_equal r1.r_type r2.r_type
  && EcPath.p_equal r1.r_zero r2.r_zero
  && EcPath.p_equal r1.r_one  r2.r_one
  && EcPath.p_equal r1.r_add  r2.r_add
  && EcUtils.oall2 EcPath.p_equal r1.r_opp r2.r_opp
  && EcPath.p_equal r1.r_mul  r2.r_mul
  && EcUtils.oall2 EcPath.p_equal r1.r_exp  r2.r_exp
  && EcUtils.oall2 EcPath.p_equal r1.r_sub r2.r_sub
  && kind_equal r1.r_kind r2.r_kind
  && match r1.r_embed, r2.r_embed with
    | `Direct  , `Direct   -> true
    | `Embed p1, `Embed p2 -> EcPath.p_equal p1 p2
    | `Default , `Default  -> true
    | _        , _         -> false


type field = {
  f_ring : ring;
  f_inv  : EcPath.path;
  f_div  : EcPath.path option;
}

let field_equal f1 f2 =
     ring_equal f1.f_ring f2.f_ring
  && EcPath.p_equal f1.f_inv f2.f_inv
  && EcUtils.oall2 EcPath.p_equal f1.f_div f2.f_div
