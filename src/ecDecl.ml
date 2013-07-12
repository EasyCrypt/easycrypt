(* -------------------------------------------------------------------- *)
open EcDebug
open EcUtils

(* -------------------------------------------------------------------- *)
type ty_params = EcIdent.t list

type tydecl = {
  tyd_params : ty_params;
  tyd_type   : EcTypes.ty option;
}

let tydecl_dump (tyd : tydecl) =
  let params = List.map EcIdent.tostring tyd.tyd_params in

  dnode "type-declaration"
    [dleaf "parameters (%s)" (String.concat ", " params);
     dnode "body" (otolist (omap tyd.tyd_type EcTypes.ty_dump))]

(* -------------------------------------------------------------------- *)
type locals = EcIdent.t list 

type operator_kind =
  | OB_oper of EcTypes.expr option 
  | OB_pred of EcFol.form option

type operator = {
  op_tparams : EcIdent.t list;
  op_ty      : EcTypes.ty;
  op_kind    : operator_kind;
}

let opinfo_dump idump info =
  match info with
  | None -> dleaf "no operator-information"
  | Some info ->
    dnode "operator-information"
      [ dnode "data" [idump info]]

let opkind_dump (ok : operator_kind) =
  match ok with
  | OB_oper info ->
      dnode "OB_oper" [opinfo_dump EcTypes.expr_dump info]

  | OB_pred info ->
      dnode "OB_pred" [opinfo_dump EcFol.f_dump info]

let op_dump (op : operator) =
  let params = List.map EcIdent.tostring op.op_tparams in

  dnode "operator-declaration"
    [dleaf "parameters (%s)" (String.concat ", " params);
     EcTypes.ty_dump op.op_ty;
     opkind_dump op.op_kind]

(* -------------------------------------------------------------------- *)
type axiom_kind = [`Axiom | `Lemma]

type axiom = {
  ax_tparams : EcIdent.t list;
  ax_spec    : EcFol.form option;
  ax_kind    : axiom_kind;
  ax_nosmt   : bool;
}

let string_of_ax_kind = function
  | `Axiom -> "axiom"
  | `Lemma -> "lemma"

let ax_dump (ax : axiom) =
  let params = List.map EcIdent.tostring ax.ax_tparams in
  let spec_node =
    match ax.ax_spec with
    | None   -> dleaf "no-specification"
    | Some f -> dnode "specification" [EcFol.f_dump f]
  in
    dnode "axiom-declaration"
      [dleaf "parameters (%s)" (String.concat ", " params);
       dleaf "kind (%s)" (string_of_ax_kind ax.ax_kind);
       spec_node]


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
