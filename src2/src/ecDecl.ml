open EcUtils
(* -------------------------------------------------------------------- *)
type ty_params = EcIdent.t list

type tydecl = {
  tyd_params : ty_params;
  tyd_type   : EcTypes.ty option;
  }

(* -------------------------------------------------------------------- *)
type locals = EcIdent.t list 
type op_body = (locals * EcTypes.tyexpr) option
type pr_body = (locals * EcFol.form) option

type operator_body = 
  | OB_op of EcIdent.t list * EcTypes.tyexpr 
  | OB_pr of EcIdent.t list * EcFol.form 

type operator = {
  op_params : EcIdent.t list;     (* type parameters *)
  op_dom    : EcTypes.dom option; (* None means constant *)
  op_codom  : EcTypes.ty option;  (* None means predicate *)
  op_body   : operator_body option;
  op_prob   : bool;
}

let op_ctnt op = op.op_dom = None
let op_pr op = op.op_codom = None
let op_dom op = odfl [] op.op_dom
let op_codom op = 
  match op.op_codom with
  | None -> assert false
  | Some ty -> ty

let op_sig op = 
  assert (not (op_pr op));
  op_dom op, op_codom op


  
let mk_pred typ dom body = 
  let body = 
    match body with
    | None -> None
    | Some(ids,f) -> Some(OB_pr(ids,f)) in
  { op_params = typ;
    op_dom    = dom;
    op_codom  = None;
    op_body   = body;
    op_prob   = false;
  }

let mk_op typ dom codom body prob = 
  let body = 
    match body with
    | None -> None
    | Some(ids,e) -> Some(OB_op(ids,e)) in
  { op_params = typ;
    op_dom    = dom;
    op_codom  = Some codom;
    op_body   = body;
    op_prob   = prob;
  }

(* -------------------------------------------------------------------- *)
type axiom_kind = Axiom | Lemma

type axiom = {
  ax_spec : EcFol.form;                       (* formula *)
  ax_kind : axiom_kind
}
