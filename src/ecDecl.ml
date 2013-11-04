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
  | `Datatype of EcFol.form * (EcSymbols.symbol * EcTypes.ty list) list
  | `Record   of EcFol.form * (EcSymbols.symbol * EcTypes.ty) list
]

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
  | OB_pred of EcFol.form option

and opbody =
  | OP_Plain  of EcTypes.expr
  | OP_Constr of EcPath.path * int
  | OP_Record of EcPath.path
  | OP_Proj   of EcPath.path * int * int
  | OP_Fix    of opfix

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
  ax_spec    : EcFol.form option;
  ax_kind    : axiom_kind;
  ax_nosmt   : bool;
}

let string_of_ax_kind = function
  | `Axiom -> "axiom"
  | `Lemma -> "lemma"

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

(* -------------------------------------------------------------------- *)
type typeclass = {
  tc_ops : (EcIdent.t * EcTypes.ty) list;
  tc_axs : EcFol.form list;
}
