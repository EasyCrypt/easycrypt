(* -------------------------------------------------------------------- *)
open EcUtils
open EcFormat
open EcTypes
open EcFol
open EcTypesmod
open EcDecl
open EcParsetree
open EcEnv

module NameGen = EcUidgen.NameGen

module IM  = EcIdent.Map
module Mid = EcIdent.Mid

module Pp = Pprint

open Pp.Operators

(* -------------------------------------------------------------------- *)
type 'a pr = 'a -> Pprint.document

let clearbreak =
  Pp.ifflat Pp.space (Pp.hardline ^^ Pp.hardline)

(* -------------------------------------------------------------------- *)
let pr_list_map fmap sep docs =
  let sep = Pp.softbreak ^^ !^sep in
    Pp.group2 (Pp.fold1 (fun x y -> x ^^ sep ^^ y) (List.map fmap docs))

let pr_list sep docs =
  pr_list_map (fun (x : Pp.document) -> x) sep docs

let pr_seq (doc : Pp.document list) =
  Pp.fold1 (^//^) doc

let pr_hang (doc : Pp.document) =
  Pp.hang 2 doc

let pr_indent (doc : Pp.document) =
  Pp.ifflat doc (Pp.indent 2 doc)

let pr_block ~prfx ~pofx (docs : Pp.document list) =
  let docs = List.map pr_indent docs in
  let docs = Pp.fold1 (fun d1 d2 -> d1 ^^ clearbreak ^^ d2) docs in
    prfx ^^ Pp.break1 ^^ docs ^^ Pp.break1 ^^ pofx

let pr_mblocks (docs : (Pp.document list) list) =
  let docs = List.filter ((<>) []) docs in
  let docs = List.map (List.map pr_indent) docs in
  let docs = List.map (Pp.fold1 (^/^)) docs in
  let docs = Pp.fold1 (fun d1 d2 -> d1 ^^ clearbreak ^^ d2) docs in
    Pp.lbrace ^^ Pp.break1 ^^ docs ^^ Pp.break1 ^^ Pp.rbrace

let pr_dotted (doc : Pp.document) = doc ^^ Pp.dot

(* -------------------------------------------------------------------- *)
let pretty (doc : Pp.document) =
  Format.fprintf Format.err_formatter "%a@?"
    (Pp.Formatter.pretty 0.8 78) doc

(* -------------------------------------------------------------------- *)
let pp_located loc pp_elt fmt x =
  Format.fprintf fmt "%s: %a" (Location.tostring loc) pp_elt x

(* -------------------------------------------------------------------- *)
let pp_of_pr (pr : 'a pr) (fmt : Format.formatter) (x : 'a) =
  Format.fprintf fmt "%a" (Pp.Formatter.pretty 0.8 78) (pr x)

(* -------------------------------------------------------------------- *)
module type IPrettyPrinter = sig
  type t                                (* ident-2-path *)

  val short_ident : t -> EcIdent.t -> EcPath.path

  (* ------------------------------------------------------------------ *)
  val pr_type     : t -> ?vmap:NameGen.t -> ty pr
  val pr_dom      : t -> EcTypes.dom pr
  val pr_typedecl : t -> (EcIdent.t * tydecl  ) pr
  val pr_opdecl   : t -> (EcIdent.t * operator) pr
  val pr_axiom    : t -> (EcIdent.t * axiom   ) pr
  val pr_modtype  : t -> (EcIdent.t * tymod   ) pr
  val pr_module   : t -> module_expr pr
  val pr_export   : t -> EcPath.path pr
  val pr_theory   : t -> (EcIdent.t * ctheory) pr
  val pr_expr     : t -> tyexpr pr

  (* ------------------------------------------------------------------ *)
  val pp_type     : t -> ?vmap:NameGen.t -> ty pp
  val pp_dom      : t -> EcTypes.dom pp
  val pp_typedecl : t -> (EcIdent.t * tydecl  ) pp
  val pp_opdecl   : t -> (EcIdent.t * operator) pp
  val pp_axiom    : t -> (EcIdent.t * axiom   ) pp
  val pp_modtype  : t -> (EcIdent.t * tymod   ) pp
  val pp_module   : t -> module_expr pp
  val pp_export   : t -> EcPath.path pp
  val pp_theory   : t -> (EcIdent.t * ctheory) pp
  val pp_expr     : t -> tyexpr pp
end

(* -------------------------------------------------------------------- *)
module type IIdentPrinter = sig
  type t

  val short_ident : t -> EcIdent.t -> EcPath.path
end

(* -------------------------------------------------------------------- *)
let tk_as     = !^ "as"
let tk_assert = !^ "assert"
let tk_axiom  = !^ "axiom"
let tk_clone  = !^ "clone"
let tk_cnst   = !^ "cnst"
let tk_else   = !^ "else"
let tk_else   = !^ "else"
let tk_end    = !^ "end"
let tk_exists = !^ "exists"
let tk_export = !^ "export"
let tk_flip   = !^ "{0,1}"
let tk_forall = !^ "forall"
let tk_fun    = !^ "fun"
let tk_if     = !^ "if"
let tk_in     = !^ "in"
let tk_lemma  = !^ "lemma"
let tk_let    = !^ "let"
let tk_module = !^ "module"
let tk_op     = !^ "op"
let tk_pop    = !^ "pop"
let tk_pred   = !^ "pred"
let tk_then   = !^ "then"
let tk_theory = !^ "theory"
let tk_type   = !^ "type"
let tk_var    = !^ "var"
let tk_while  = !^ "while"

let tk_arrow  = !^ "->"
let tk_dotdot = !^ ".."

(* -------------------------------------------------------------------- *)
module EcPP(M : IIdentPrinter) :
  IPrettyPrinter with type t = M.t
=
struct
  module EP = EcParser

  (* ------------------------------------------------------------------ *)
  type t = M.t

  (* ------------------------------------------------------------------ *)
  let short_ident = M.short_ident

  (* ------------------------------------------------------------------ *)
  let pr_ident (_tenv : t) (x : EcIdent.t) =
    !^ (EcIdent.tostring x)

  (* ------------------------------------------------------------------ *)
  let pr_path (_tenv : t) (p : EcPath.path) =
    !^ (EcIdent.tostring (EcPath.basename p))

  (* ------------------------------------------------------------------ *)
  let pr_tvar (_tenv : t) (id : EcIdent.t) =
    !^ (EcIdent.tostring id)

  (* ------------------------------------------------------------------ *)
  let pr_tunivar (uidmap : NameGen.t) (id : EcUidgen.uid) =
    !^ (Printf.sprintf "#%s" (NameGen.get uidmap id))

  (* ------------------------------------------------------------------ *)
  let pr_tuple docs =
    match docs with
    | []    -> Pp.empty
    | [doc] -> doc
    | _     -> Pp.parens (pr_list "," docs)

  (* ------------------------------------------------------------------ *)
  let pr_type (tenv : t) (uidmap : NameGen.t) (ty : ty) =
    let rec pr_type btuple = function
      | Tvar id ->
          pr_tvar tenv id

      | Tunivar id ->
          pr_tunivar uidmap id

      | Ttuple tys ->
          let doc = pr_list_map (pr_type true) "* " tys in (* FIXME "*" *)
            if btuple then Pp.parens doc else doc

      | Tconstr (name, tyargs) -> begin
          match tyargs with
          | [] -> pr_path tenv name
          | _  -> (pr_tuple (List.map (pr_type false) tyargs))
                  ^//^ (pr_path tenv name)
      end
    in
      pr_type false ty

  (* ------------------------------------------------------------------ *)
  let pr_type (tenv : t) ?(vmap : _ option) (ty : ty) =
    let uidmap =
      match vmap with
      | None        -> NameGen.create ()
      | Some uidmap -> uidmap
    in
      pr_type tenv uidmap ty

  (* ------------------------------------------------------------------ *)
  type assoc  = [`Left | `Right | `NonAssoc]
  type fixity = [`Prefix | `Postfix | `Infix of assoc]
  type opprec = int * fixity

  (* ------------------------------------------------------------------ *)
  let bracket (outer, side) inner doc =
    let noparens ((pi, fi) as _inner) ((po, fo) as _outer) side =
      (pi > po) ||
        match fi, side with
        | `Postfix     , `Left     -> true
        | `Prefix      , `Right    -> true
        | `Infix `Left , `Left     -> (pi = po) && (fo = `Infix `Left )
        | `Infix `Right, `Right    -> (pi = po) && (fo = `Index `Right)
        | _            , `NonAssoc -> fi = fo
        | _            , _         -> false
    in
      match noparens inner outer side with
      | true  -> doc
      | false -> Pp.parens doc

  (* ------------------------------------------------------------------ *)
  let e_bin_prio_impl   = (10, `Infix `Right)
  let e_bin_prio_if     = (15, `Prefix)
  let e_bin_prio_if3    = (17, `Infix `NonAssoc)
  let e_bin_prio_letin  = (19, `Prefix)
  let e_bin_prio_or     = (20, `Infix `Right)
  let e_bin_prio_and    = (25, `Infix `Right)
  let e_bin_prio_eq     = (27, `Infix `NonAssoc)
  let e_bin_prio_op1    = (30, `Infix `Left)  (* FIXME: really ? *)
  let e_bin_prio_op2    = (40, `Infix `Left)  (* FIXME: really ? *)
  let e_bin_prio_op3    = (50, `Infix `Left)  (* FIXME: really ? *)
  let e_bin_prio_op4    = (60, `Infix `Left)  (* FIXME: really ? *)

  let e_uni_prio_not    =  26
  let e_uni_prio_uminus = 500

  let e_prio_excpt = (1000, `Infix `NonAssoc)

  let min_op_prec = (-1     , `Infix `NonAssoc)
  let max_op_prec = (max_int, `Infix `NonAssoc)

  (* ------------------------------------------------------------------ *)
  let priority_of_binop_name name =
    match EcIo.lex_single_token name with
    | Some EP.IMPL  -> Some e_bin_prio_impl
    | Some EP.IFF   -> Some e_bin_prio_impl
    | Some EP.OR    -> Some e_bin_prio_or
    | Some EP.AND   -> Some e_bin_prio_and
    | Some EP.EQ    -> Some e_bin_prio_eq
    | Some EP.NE    -> Some e_bin_prio_eq
    | Some EP.OP1 _ -> Some e_bin_prio_op1
    | Some EP.OP2 _ -> Some e_bin_prio_op2
    | Some EP.MINUS -> Some e_bin_prio_op3
    | Some EP.OP3 _ -> Some e_bin_prio_op3
    | Some EP.STAR  -> Some e_bin_prio_op3
    | Some EP.OP4 _ -> Some e_bin_prio_op4

    | _ -> None

  (* ------------------------------------------------------------------ *)
  let priority_of_uniop name =
    match EcIo.lex_single_token name with
    | Some EP.MINUS -> Some e_uni_prio_uminus
    | Some EP.NOT   -> Some e_uni_prio_not
    | _  -> None

  (* ------------------------------------------------------------------ *)
  let is_binop name =
    (priority_of_binop_name name) <> None

  (* ------------------------------------------------------------------ *)
  let pr_vardecl (tenv : t) (x, ty) =
    pr_seq [pr_ident tenv x; Pp.colon; pr_type tenv ty]

  (* ------------------------------------------------------------------ *)
  let pr_vardecls (tenv : t) d =
    Pp.parens (pr_list ", " (List.map (pr_vardecl tenv) d))

  (* ------------------------------------------------------------------ *)
  let pr_if3 (tenv : t) pr_sub outer b e1 e2 =
    let dc  = pr_sub tenv (e_bin_prio_if3, `Left    ) b  in
    let d1  = pr_sub tenv (min_op_prec   , `NonAssoc) e1 in
    let d2  = pr_sub tenv (e_bin_prio_if3, `Right   ) e2 in
    let doc = pr_seq [dc; Pp.qmark; d1; Pp.colon; d2] in
      bracket outer e_bin_prio_if3 doc

  (* ------------------------------------------------------------------ *)
  let pr_if (tenv : t) pr_sub outer b e1 e2 =
    let dc  = pr_sub tenv (min_op_prec  , `NonAssoc) b  in
    let d1  = pr_sub tenv (min_op_prec  , `NonAssoc) e1 in
    let d2  = pr_sub tenv (e_bin_prio_if, `Right   ) e2 in
    let doc = pr_seq [tk_if; dc; tk_then; d1; tk_else; d2] in
      bracket outer e_bin_prio_if doc

  (* ------------------------------------------------------------------ *)
  let pr_let (tenv : t) pr_sub outer pt e1 e2 =
    let dpt =
      match pt with
      | LSymbol x  -> pr_ident tenv x
      | LTuple  xs -> pr_tuple (List.map (pr_ident tenv) xs)
    in
    let d1  = pr_sub tenv (e_bin_prio_letin, `NonAssoc) e1 in
    let d2  = pr_sub tenv (e_bin_prio_letin, `NonAssoc) e2 in (* FIXME: binding *)
    let doc = pr_seq [tk_let; dpt; Pp.equals; d1; tk_in; d2] in
      bracket outer e_bin_prio_letin doc

  (* ------------------------------------------------------------------ *)
  let pr_tuple_expr (tenv : t) pr_sub es =
    let docs = List.map (pr_sub tenv (min_op_prec, `NonAssoc)) es in
      Pp.parens (pr_list ", " docs)

  (* ------------------------------------------------------------------ *)
  let pr_app (tenv : t) pr_sub outer op es =
    let opname = EcIdent.name (EcPath.basename op) in

    let pr_as_std_op () =
      match es with
      | [] -> pr_path tenv op
      | _  ->
          let docs = List.map (pr_sub tenv (min_op_prec, `NonAssoc)) es in
          (pr_path tenv op) ^^ pr_seq [Pp.parens (pr_list "," docs)]

    and try_pr_as_uniop () =
      match es with
      | [e] ->
          begin match priority_of_uniop opname with
          | None -> None
          | Some opprio  ->
              let opprio = (opprio, `Prefix) in
              let doc    = !^opname ^^ (pr_sub tenv (opprio, `NonAssoc) e) in
                Some (bracket outer opprio doc)
          end

      | _ -> None

    and try_pr_as_binop () =
      match es with
      | [e1; e2] ->
          begin match priority_of_binop_name opname with
          | None -> None
          | Some opprio ->
              let d1  = pr_sub tenv (opprio, `Left ) e1 in
              let d2  = pr_sub tenv (opprio, `Right) e2 in
              let doc = pr_seq [d1; !^ opname; d2] in
                Some (bracket outer opprio doc)
          end

      | _ -> None
    in
      ofdfl pr_as_std_op
        (List.fpick [try_pr_as_uniop; try_pr_as_binop])

  (* ------------------------------------------------------------------ *)
  let pr_expr (tenv : t) (e : tyexpr) =
    let rec pr_expr (tenv : t) outer (e : tyexpr) =
        match e.tye_desc with
        | Evar (x, _) ->
            pr_path tenv x.pv_name

        | Elocal (x, _) ->
            pr_ident tenv x

        | Eint i ->
            Pp.ML.int i

        | Eflip ->
            tk_flip

        | Eexcepted (e1, e2) ->
            let d1 = pr_expr tenv (e_prio_excpt, `Left ) e1 in
            let d2 = pr_expr tenv (e_prio_excpt, `Right) e2 in
              Pp.parens (pr_seq [d1; Pp.backslash; d2])

        | Ebitstr e ->
            let d = pr_expr tenv (min_op_prec, `NonAssoc) e in
              pr_seq [tk_flip; Pp.caret; Pp.parens d]

        | Einter (e1, e2) ->
            let d1 = pr_expr tenv (min_op_prec, `NonAssoc) e1 in
            let d2 = pr_expr tenv (min_op_prec, `NonAssoc) e2 in
              Pp.brackets (pr_hang (pr_seq [d1; tk_dotdot; d2]))

        | Eif (c, e1, e2) ->
            pr_if tenv pr_expr outer c e1 e2

        | Etuple es ->
            pr_tuple_expr tenv pr_expr es

        | Eapp (op, es, _) ->
            pr_app tenv pr_expr outer op es

        | Elet (pt, e1, e2) ->
            pr_let tenv pr_expr outer pt e1 e2

    in
      pr_expr tenv (min_op_prec, `NonAssoc) e

  (* ------------------------------------------------------------------ *)
  let tk_quant = function
    | Lforall -> tk_forall
    | Lexists -> tk_exists

  (* ------------------------------------------------------------------ *)
  let pr_form (tenv : t) (f : form) =
    let rec pr_form (tenv : t) outer (f : form) =
      match f.f_node with
      | Fint n ->
          Pp.ML.int n

      | Flocal id ->
          pr_ident tenv id

      | Fpvar (x, _, i) ->
          pr_seq [pr_path tenv x.pv_name; Pp.braces (Pp.ML.int i)]

      | Fquant(q, bd, f) ->             (* FIXME: binding *)
          pr_seq [tk_quant q;
                  pr_vardecls tenv bd;
                  Pp.comma;
                  pr_form tenv outer f]

      | Fif(b, f1, f2) ->
          pr_if tenv pr_form outer b f1 f2

      | Flet(lp, f1, f2) ->
          pr_let tenv pr_form outer lp f1 f2

      | Fapp(p, args) ->
          pr_app tenv pr_form outer p args

      | Ftuple args ->
          pr_tuple_expr tenv pr_form args
    in
      pr_form tenv (min_op_prec, `NonAssoc) f

  (* ------------------------------------------------------------------ *)
  let pr_typedecl (tenv : t) ((x, tyd) : EcIdent.t * tydecl) =
    let dparams =  
      if tyd.tyd_params = [] then Pp.empty 
      else Pp.parens (pr_list_map (pr_tvar tenv) ", " tyd.tyd_params) in
    let doc = tk_type ^//^ dparams ^^ (pr_ident tenv x) in 
    let doc =
      match tyd.tyd_type with
      | None    -> doc
      | Some ty -> doc ^//^ Pp.equals ^//^ (pr_type tenv ty)
    in
      pr_dotted (Pp.nest 2 doc)

  (* ------------------------------------------------------------------ *)
  let pr_dom (tenv : t) dom =
    pr_tuple (List.map (pr_type tenv) dom)

  (* ------------------------------------------------------------------ *)
  let pr_sig (tenv : t) (dom, codom) =
    match dom with
    | [] -> pr_type tenv codom
    | _  -> (pr_dom tenv dom) ^//^ tk_arrow ^//^ (pr_type tenv codom)

  (* ------------------------------------------------------------------ *)
  let pr_tyvarsdecl (tenv : t) ids =
    if ids = [] then
      Pp.empty
    else
      Pp.brackets (pr_seq (List.map (pr_tvar tenv) ids))

  (* ------------------------------------------------------------------ *)
  let pr_opdecl (tenv : t) ((x, op) : EcIdent.t * operator) =
    let dop, ddecl =
      match op.op_kind with
      | OB_oper i ->
          let dop = if op.op_dom = [] then tk_cnst else tk_op in
          let ddecl =
            match i.op_def with
            | None -> pr_seq [Pp.colon; pr_sig tenv (op_sig op)]
            | Some (ids, e) ->
                let vardecls = List.combine ids op.op_dom in
                pr_seq [pr_vardecls tenv vardecls;
                        Pp.colon;
                        pr_type tenv op.op_codom;
                        Pp.equals;
                        pr_expr tenv e]
          in
            (dop, ddecl)

      | OB_pred i ->
          let ddecl =
            match i.op_def with
            | None -> pr_seq [Pp.colon; pr_dom tenv op.op_dom]
            | Some (ids,_f) ->
                let vardecls = List.combine ids op.op_dom in
                pr_seq [pr_vardecls tenv vardecls; Pp.equals (* FIXME pp_form f *)]
          in
          tk_pred, ddecl
      | OB_prob _ -> assert false         (* FIXME: no parsing rule *) in
    let doc = pr_seq [dop; pr_ident tenv x; pr_tyvarsdecl tenv op.op_params; ddecl] in
    pr_dotted doc

  (* ------------------------------------------------------------------ *)
  let pr_axiom (tenv : t) ((x, ax) : EcIdent.t * axiom) =
    let tk =                            (* FIXME: var bindings *)
      match ax.ax_kind with
      | Axiom   -> tk_axiom
      | Lemma _ -> tk_lemma

    and pr_name =
      match ax.ax_params with
      | [] -> pr_ident tenv x
      | _  ->    (pr_ident tenv x)
              ^^ (Pp.angles (pr_list_map (pr_ident tenv) "," ax.ax_params))

    and spec =
      match ax.ax_spec with
      | None   -> !^"<why3-imported>"
      | Some f -> pr_form tenv f
    in

      pr_seq [tk; pr_name; Pp.colon; spec]

  (* ------------------------------------------------------------------ *)
  let pr_modtype (tenv : t) ((x, _tymod) : EcIdent.t * tymod) =
    pr_dotted (pr_seq [tk_module; tk_type; pr_ident tenv x; Pp.equals])

  (* ------------------------------------------------------------------ *)
  let pr_variable (tenv : t) (x : variable) =
    pr_seq [tk_var; pr_ident tenv x.v_name; Pp.colon; pr_type tenv x.v_type]

  (* ------------------------------------------------------------------ *)
  let pr_local (tenv : t) (x : EcIdent.t) (ty : ty) =
    pr_seq [pr_ident tenv x; Pp.colon; pr_type tenv ty] ^^ Pp.semi

  (* ------------------------------------------------------------------ *)
  let pr_instr (tenv : t) (i : instr) =
    let doc =
      match i with
      | Sasgn (LvVar (x, _), e) ->
          pr_seq [pr_path tenv x; Pp.equals; pr_expr tenv e]

      | Scall (None, p, args) ->
          (pr_path tenv p) ^^ (Pp.parens (pr_list_map (pr_expr tenv) "," args))

      | Sassert e ->
          pr_seq [tk_assert; Pp.parens (pr_expr tenv e)]

      | Sif (e, _b1, _b2) ->
          pr_seq [tk_if; Pp.parens (pr_expr tenv e)]

      | Swhile (e, _body) ->
          pr_seq [tk_while; Pp.parens (pr_expr tenv e)]

      | _ -> assert false

    in
      doc ^^ Pp.semi

  (*
    | Scall   of lvalue option * EcPath.path * EcTypes.tyexpr list
  *)

  (* ------------------------------------------------------------------ *)
  let pr_function (tenv : t) (f : function_) = (* FIXME: tenv bindings *)
    let fname = f.f_sig.fs_name in
    let fparams, fres = f.f_sig.fs_sig in

    let dparams =
      List.map
        (fun (x, ty) -> pr_seq [pr_ident tenv x; Pp.colon; pr_type tenv ty])
        fparams in
    let dparams = Pp.parens (pr_list "," dparams) in

    let prelude =
      pr_seq [tk_fun; !^fname ^^ dparams; Pp.colon; pr_type tenv fres]
    in

    let dlocals = List.map (fun (x, ty) -> pr_local tenv x ty) f.f_locals
    and dbody   = List.map (pr_instr tenv) f.f_body in

      (pr_seq [prelude; Pp.equals]) ^/^ (pr_mblocks [dlocals; dbody])

  (* ------------------------------------------------------------------ *)
  let rec pr_module_item (tenv : t) (item : module_item) =
    match item with
    | `Variable x  -> pr_variable tenv x
    | `Function f  -> pr_function tenv f
    | `Module   me -> pr_module   tenv me

  (* ------------------------------------------------------------------ *)
  and pr_module (tenv : t) (m : module_expr) = (* FIXME: bindings *)
    let mename  = m.me_name in
    let prelude = pr_seq [tk_module; pr_ident tenv mename] in
    let moddoc  =
      match m.me_body with
      | ME_Ident x ->
          pr_seq [prelude; Pp.equals; pr_path tenv x]

      | ME_Application (p, args) ->
          let dargs = Pp.parens (pr_list_map (pr_path tenv) "," args) in
          let dbody = (pr_path tenv p) ^^ dargs in
            pr_seq [prelude; Pp.equals; dbody]

      | ME_Decl p ->
          pr_seq [prelude; Pp.colon; pr_path tenv p]

      | ME_Structure mstruct ->
          let bodydoc = List.map (pr_module_item tenv) mstruct.ms_body in
                (pr_seq [prelude; Pp.equals])
            ^/^ (pr_block Pp.lbrace Pp.rbrace bodydoc)
    in
      pr_dotted moddoc

  (* ------------------------------------------------------------------ *)
  let pr_export (tenv : t) (p : EcPath.path) =
    pr_dotted (tk_export ^//^ (pr_path tenv p))

  (* ------------------------------------------------------------------ *)
  let rec pr_ctheory_item (tenv : t) (item : ctheory_item) =
    match item with
    | CTh_type     (x, ty) -> pr_typedecl tenv (x, ty)
    | CTh_operator (x, op) -> pr_opdecl   tenv (x, op)
    | CTh_axiom    (x, ax) -> pr_axiom    tenv (x, ax)
    | CTh_modtype  (x, ty) -> pr_modtype  tenv (x, ty)
    | CTh_module   m       -> pr_module   tenv m
    | CTh_theory   (x, th) -> pr_theory   tenv (x, th)
    | CTh_export   p       -> pr_export   tenv p

  (* ------------------------------------------------------------------ *)
  and pr_theory (tenv : t) ((name, ctheory) : EcIdent.t * ctheory) =
    match ctheory.cth_desc with
    | CTh_clone p ->
        tk_clone ^//^ (pr_path tenv p) ^//^ tk_as ^//^ (pr_ident tenv name)

    | CTh_struct cstruct ->
        let pr_cstruct = List.map (pr_ctheory_item tenv) cstruct in
          pr_block
            ~prfx:(pr_dotted (tk_theory ^//^ (pr_ident tenv name)))
            ~pofx:(pr_dotted (tk_end    ^//^ (pr_ident tenv name)))
            pr_cstruct

  (* ------------------------------------------------------------------ *)
  let pp_type     = fun t ?vmap -> pp_of_pr (pr_type t ?vmap)
  let pp_dom      = fun t -> pp_of_pr (pr_dom t)
  let pp_typedecl = fun t -> pp_of_pr (pr_typedecl t)
  let pp_opdecl   = fun t -> pp_of_pr (pr_opdecl t)
  let pp_axiom    = fun t -> pp_of_pr (pr_axiom t)
  let pp_modtype  = fun t -> pp_of_pr (pr_modtype t)
  let pp_module   = fun t -> pp_of_pr (pr_module t)
  let pp_export   = fun t -> pp_of_pr (pr_export t)
  let pp_theory   = fun t -> pp_of_pr (pr_theory t)
  let pp_expr     = fun t -> pp_of_pr (pr_expr t)
end

(* -------------------------------------------------------------------- *)
module RawIndentPrinter : IIdentPrinter with type t = unit =
struct
  type t = unit

  let short_ident (_ : t) (x : EcIdent.t) =
    EcPath.Pident x
end

(* -------------------------------------------------------------------- *)
module EcRawPP = struct
  module BPP = EcPP(RawIndentPrinter)

  let pr_type     = BPP.pr_type     ()
  let pr_dom      = BPP.pr_dom      ()
  let pr_typedecl = BPP.pr_typedecl ()
  let pr_opdecl   = BPP.pr_opdecl   ()
  let pr_axiom    = BPP.pr_axiom    ()
  let pr_modtype  = BPP.pr_modtype  ()
  let pr_module   = BPP.pr_module   ()
  let pr_export   = BPP.pr_export   ()
  let pr_theory   = BPP.pr_theory   ()
  let pr_expr     = BPP.pr_expr     ()

  let pp_type     = BPP.pp_type     ()
  let pp_dom      = BPP.pp_dom      ()
  let pp_typedecl = BPP.pp_typedecl ()
  let pp_opdecl   = BPP.pp_opdecl   ()
  let pp_axiom    = BPP.pp_axiom    ()
  let pp_modtype  = BPP.pp_modtype  ()
  let pp_module   = BPP.pp_module   ()
  let pp_export   = BPP.pp_export   ()
  let pp_theory   = BPP.pp_theory   ()
  let pp_expr     = BPP.pp_expr     ()

  let rec pp_qsymbol fmt = function
    | ([]    , x) -> Format.fprintf fmt "%s" x
    | (n :: p, x) -> Format.fprintf fmt "%s.%a" n pp_qsymbol (p, x)

  let rec pp_path fmt = function
    | EcPath.Pident x      -> Format.fprintf fmt "%s" (EcIdent.name x)
    | EcPath.Pqname (p, x) -> Format.fprintf fmt "%a.%s" pp_path p (EcIdent.name x)
end
