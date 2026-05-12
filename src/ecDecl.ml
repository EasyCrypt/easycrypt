(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcTypes
open EcCoreFol

module Sp   = EcPath.Sp
module BI   = EcBigInt
module Ssym = EcSymbols.Ssym
module CS   = EcCoreSubst

(* -------------------------------------------------------------------- *)
type ty_param  = EcIdent.t * typeclass list
type ty_params = ty_param list
type ty_pctor  = [ `Int of int | `Named of ty_params ]

type ty_record =
  EcCoreFol.form * (EcSymbols.symbol * EcTypes.ty) list

type ty_dtype_ctor =
  EcSymbols.symbol * EcTypes.ty list

type ty_dtype = {
  tydt_ctors   : ty_dtype_ctor list;
  tydt_schelim : EcCoreFol.form;
  tydt_schcase : EcCoreFol.form;
}

type ty_body = [
  | `Concrete of EcTypes.ty
  | `Abstract of typeclass list
  | `Datatype of ty_dtype
  | `Record   of ty_record
]


type tydecl = {
  tyd_params  : ty_params;
  tyd_type    : ty_body;
  tyd_resolve : bool;
  tyd_loca    : locality;
  tyd_subtype : (EcTypes.ty * EcCoreFol.form) option;
}

let tydecl_as_concrete (td : tydecl) =
  match td.tyd_type with `Concrete x -> Some x | _ -> None

let tydecl_as_abstract (td : tydecl) =
  match td.tyd_type with `Abstract x -> Some x | _ -> None

let tydecl_as_datatype (td : tydecl) =
  match td.tyd_type with `Datatype x -> Some x | _ -> None

let tydecl_as_record (td : tydecl) =
  match td.tyd_type with `Record x -> Some x | _ -> None

(* -------------------------------------------------------------------- *)
let abs_tydecl ?(resolve = true) ?(tc = []) ?(params = `Int 0) lc =
  let params =
    match params with
    | `Named params ->
        params
    | `Int n ->
        let fmt = fun x -> Printf.sprintf "'%s" x in
        List.map
          (fun x -> (EcIdent.create x, []))
          (EcUid.NameGen.bulk ~fmt n)
  in

  { tyd_params  = params;
    tyd_type    = `Abstract tc;
    tyd_resolve = resolve;
    tyd_loca    = lc;
    tyd_subtype = None; }

(* -------------------------------------------------------------------- *)
let etyargs_of_tparams (tps : ty_params) : etyarg list =
  List.map (fun (a, tcs) ->
    let ety =
      List.mapi (fun offset _ -> TCIAbstract { support = `Var a; offset; lift = [] }) tcs
    in (tvar a, ety)
  ) tps

(* -------------------------------------------------------------------- *)
let ty_instanciate (params : ty_params) (args : etyarg list) (ty : ty) =
  let subst = CS.Tvar.init (List.combine (List.map fst params) args) in
  CS.Tvar.subst subst ty

(* -------------------------------------------------------------------- *)
type locals = EcIdent.t list

type operator_kind =
  | OB_oper of opbody option
  | OB_pred of prbody option
  | OB_nott of notation

and opbody =
  | OP_Plain  of EcCoreFol.form
  | OP_Constr of EcPath.path * int
  | OP_Record of EcPath.path
  | OP_Proj   of EcPath.path * int * int
  | OP_Fix    of opfix
  | OP_Exn    of ty list
  | OP_TC     of EcPath.path * string

and prbody =
  | PR_Plain of form
  | PR_Ind   of prind

and opfix = {
  opf_recp     : EcPath.path;
  opf_args     : (EcIdent.t * EcTypes.ty) list;
  opf_resty    : EcTypes.ty;
  opf_struct   : int list * int;
  opf_branches : opbranches;
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
  op_tparams  : ty_params;
  op_ty       : EcTypes.ty;
  op_kind     : operator_kind;
  op_loca     : locality;
  op_opaque   : opopaque;
  op_clinline : bool;
  op_unfold   : int option;
}

and opopaque = { smt: bool; reduction: bool; }

(* -------------------------------------------------------------------- *)
type axiom_kind = [`Axiom of (Ssym.t * bool) | `Lemma]

type axiom = {
  ax_tparams : ty_params;
  ax_spec    : EcCoreFol.form;
  ax_kind    : axiom_kind;
  ax_loca    : locality;
  ax_smt     : bool; }

let is_axiom  (x : axiom_kind) = match x with `Axiom _ -> true | _ -> false
let is_lemma  (x : axiom_kind) = match x with `Lemma   -> true | _ -> false

(* -------------------------------------------------------------------- *)
type exception_ = {
  exn_loca : locality;
  exn_dom  : ty list;
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

let is_tc_op op =
  match op.op_kind with
  | OB_oper (Some (OP_TC _)) -> true
  | _ -> false

let is_fix op =
  match op.op_kind with
  | OB_oper (Some (OP_Fix _)) -> true
  | _ -> false

let is_exception op =
  match op.op_kind with
  | OB_oper (Some (OP_Exn _)) -> true
  | _ -> false

let is_abbrev op =
  match op.op_kind with
  | OB_nott _ -> true
  | _ -> false

let is_prind op =
  match op.op_kind with
  | OB_pred (Some (PR_Ind _)) -> true
  | _ -> false

let gen_op ?(clinline = false) ?unfold ~opaque tparams ty kind lc = {
  op_tparams  = tparams;
  op_ty       = ty;
  op_kind     = kind;
  op_loca     = lc;
  op_opaque   = opaque;
  op_clinline = clinline;
  op_unfold   = unfold;
}

let mk_pred ?clinline ?unfold ~opaque tparams dom body lc =
  let kind = OB_pred body in
  let ty   =  (EcTypes.toarrow dom EcTypes.tbool) in
  gen_op ?clinline ?unfold ~opaque tparams ty kind lc

let optransparent : opopaque =
  { smt = false; reduction = false; }

let mk_op ?clinline ?unfold ~opaque tparams ty body lc =
  let kind = OB_oper body in
  gen_op ?clinline ?unfold ~opaque tparams ty kind lc

let mk_exception (exn_loca : locality) (exn_dom : ty list) : exception_ =
  { exn_loca; exn_dom; }

let mk_abbrev ?(ponly = false) tparams xs (codom, body) lc =
  let kind = {
    ont_args  = xs;
    ont_resty = codom;
    ont_body  = body;
    ont_ponly = ponly;
  } in

  gen_op ~opaque:optransparent tparams
    (EcTypes.toarrow (List.map snd xs) codom) (OB_nott kind) lc

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

let operator_as_tc (op : operator) =
  match op.op_kind with
  | OB_oper (Some (OP_TC (tcpath, name))) -> (tcpath, name)
  | _ -> assert false

let operator_as_exception (op : operator) =
  match op.op_kind with
  | OB_oper (Some (OP_Exn exn_dom)) ->
      { exn_loca = op.op_loca; exn_dom; }
  | _ -> assert false

let operator_of_exception (ex: exception_) =
  let ty = EcTypes.toarrow ex.exn_dom EcTypes.texn in
  mk_op ~opaque: optransparent [] ty (Some (OP_Exn ex.exn_dom)) ex.exn_loca

(* -------------------------------------------------------------------- *)
(* A parent typeclass plus an optional op renaming. The renaming maps
   the parent's op names (recursively, including its own ancestors)
   to op names declared in or inherited by the subclass — used to
   project a subclass instance into a parent instance with different
   operator names. Empty list = plain inheritance. *)
type tc_decl = {
  tc_tparams : ty_params;
  (* Per parent-edge: the typeclass instantiation, an optional label
     (defaulting to the parent's bare class name), and the rename
     clause. The label disambiguates obligations reaching the
     instance through multiple parent edges of the same class. *)
  tc_prts    : (typeclass * EcSymbols.symbol
                * (EcSymbols.symbol * EcSymbols.symbol) list) list;
  tc_ops     : (EcIdent.t * EcTypes.ty) list;
  tc_axs     : (EcSymbols.symbol * EcCoreFol.form) list;
  tc_loca    : is_local;
  (* Origin tracking for [tc_ops]: maps each op's local name to its
     "canonical source" — the (ancestor class path, original op name)
     pair where this op was first introduced. User-declared ops have
     origin [(self_path, local_name)]; auto-promoted renamed ops
     inherit origin from the ancestor whose op they alias. Used by
     downstream classes' auto-import to dedupe ops reached via
     multiple inheritance paths. *)
  tc_ops_origin : (EcSymbols.symbol * (EcPath.path * EcSymbols.symbol)) list;
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
