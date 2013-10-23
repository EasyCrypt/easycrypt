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
  | `Datatype of (EcSymbols.symbol * EcTypes.ty list) list
]

(* -------------------------------------------------------------------- *)
type locals = EcIdent.t list 

type operator_kind =
  | OB_oper of opbody option
  | OB_pred of EcFol.form option

and opbody =
  | OP_Plain  of EcTypes.expr
  | OP_Constr of EcPath.path * int

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
 
let gen_op tparams ty kind = 
  { op_tparams = tparams;
    op_ty      = ty;
    op_kind    = kind;
  }

let mk_pred tparams dom body =
  let kind = OB_pred body in
    gen_op tparams (EcTypes.toarrow dom EcTypes.tbool) kind

let mk_op tparams ty body = 
  let kind = OB_oper body in
    gen_op tparams ty kind

(* -------------------------------------------------------------------- *)
type typeclass = {
  tc_ops : (EcIdent.t * EcTypes.ty) list;
  tc_axs : EcFol.form list;
}
