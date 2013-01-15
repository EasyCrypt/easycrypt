open EcUtils
(* -------------------------------------------------------------------- *)
type ty_params = EcIdent.t list

type tydecl = {
  tyd_params : ty_params;
  tyd_type   : EcTypes.ty option;
}

(* -------------------------------------------------------------------- *)
type locals = EcIdent.t list 

type ('b,'info) operator_info = {
    op_def : (locals * 'b) option;
    op_info : 'info (* extra information used for pop *)
  }

type operator_kind = 
  | OB_oper of (EcTypes.tyexpr, unit) operator_info
  | OB_pred of (EcFol.form    , unit) operator_info
  | OB_prob of (EcTypes.tyexpr, unit) operator_info

type operator = {
  op_params : EcIdent.t list;     (* type parameters *)
  op_dom    : EcTypes.dom;        
  op_codom  : EcTypes.ty;
  op_kind   : operator_kind;
}

let op_sig op = op.op_dom, op.op_codom

let is_oper op = 
  match op.op_kind with
  | OB_oper _ -> true
  | _ -> false

let is_ctnt op = is_oper op && op.op_dom = []

let is_pred op = 
  match op.op_kind with
  | OB_pred _ -> true
  | _ -> false
 
let is_prob op = 
  match op.op_kind with
  | OB_prob _ -> true
  | _         -> false  

let gen_op tparams dom codom kind = 
  { op_params = tparams;
    op_dom    = dom;
    op_codom  = codom;
    op_kind   = kind;
  }

let mk_pred tparams dom body = 
  let kind = OB_pred({op_def = body; op_info = () }) in
  gen_op tparams dom EcTypes.tbool kind

let mk_op tparams dom codom body prob = 
  let kind = 
    if prob then OB_prob({op_def = body; op_info = ()})
    else OB_oper({op_def = body;op_info = ()}) in
  gen_op tparams dom codom kind

(* -------------------------------------------------------------------- *)
type axiom_kind = 
  | Axiom 
  | Lemma of EcFol.judgment option (* None means cloned lemma *)

type axiom = {
  ax_params : EcIdent.t list;  (* type parameters *)
  ax_spec : EcFol.form option; (* formula *) (* None means that we can not build its value from why3 *)
  ax_kind : axiom_kind
}
