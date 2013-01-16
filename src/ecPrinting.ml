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

(** {2 PP-style printers} *)

(* -------------------------------------------------------------------- *)
type 'a pr = 'a -> Pprint.document

module Pp = Pprint

open Pp.Operators

let clearbreak =
  Pp.ifflat Pp.space (Pp.hardline ^^ Pp.hardline)

(* -------------------------------------------------------------------- *)
let tk_axiom  = !^ "axiom"
let tk_as     = !^ "as"
let tk_clone  = !^ "clone"
let tk_else   = !^ "else"
let tk_end    = !^ "end"
let tk_export = !^ "export"
let tk_flip   = !^ "{0,1}"
let tk_if     = !^ "if"
let tk_then   = !^ "then"
let tk_else   = !^ "else"
let tk_in     = !^ "in"
let tk_lemma  = !^ "lemma"
let tk_let    = !^ "let"
let tk_module = !^ "module"
let tk_cnst   = !^ "cnst"
let tk_op     = !^ "op"
let tk_pop    = !^ "pop"
let tk_pred   = !^ "pred"
let tk_theory = !^ "theory"

let tk_type   = !^ "type"

let tk_arrow  = !^ "->"
let tk_dotdot = !^ ".."

let tk_forall = !^ "forall"
let tk_exists = !^ "exists"

let tk_quant = function
  | Lforall -> tk_forall
  | Lexists -> tk_exists

(* -------------------------------------------------------------------- *)
let pr_list_map fmap sep docs =
  let sep = Pp.softbreak ^^ !^sep in
    Pp.group2 (Pp.fold1 (fun x y -> x ^^ sep ^^ y) (List.map fmap docs))

(* -------------------------------------------------------------------- *)
let pr_list sep docs =
  pr_list_map (fun (x : Pp.document) -> x) sep docs

(* -------------------------------------------------------------------- *)
let pr_ident (x : EcIdent.t) =
  !^ (EcIdent.tostring x)

(* -------------------------------------------------------------------- *)
let pr_path (p : EcPath.path) =
  !^ (EcIdent.tostring (EcPath.basename p))

(* -------------------------------------------------------------------- *)
let pr_tvar (id : EcIdent.t) =
  !^ (EcIdent.tostring id)

(* -------------------------------------------------------------------- *)
let pr_tunivar (uidmap : NameGen.t) (id : EcUidgen.uid) =
  !^ (Printf.sprintf "#%s" (NameGen.get uidmap id))

(* -------------------------------------------------------------------- *)
let pr_tuple docs =
  match docs with
  | []    -> Pp.empty
  | [doc] -> doc
  | _     -> Pp.parens (pr_list "," docs)

(* -------------------------------------------------------------------- *)
let pr_type (uidmap : NameGen.t) (ty : ty) =
  let rec pr_type btuple = function
    | Tvar    id -> pr_tvar id
    | Tunivar id -> pr_tunivar uidmap id

    | Ttuple tys ->
        let doc = pr_list_map (pr_type true) "* " tys in (* FIXME "*" *)
          if btuple then Pp.parens doc else doc

    | Tconstr (name, tyargs) -> begin
        match tyargs with
        | [] -> pr_path name
        | _  -> (pr_tuple (List.map (pr_type false) tyargs))
                ^//^ (pr_path name)
    end
  in
    pr_type false ty

(* -------------------------------------------------------------------- *)
let pr_type ?(vmap : _ option) (ty : ty) =
  let uidmap =
    match vmap with
    | None        -> NameGen.create ()
    | Some uidmap -> uidmap
  in
    pr_type uidmap ty

(* -------------------------------------------------------------------- *)
let e_prio_base   = 0
let e_prio_impl   = 1
let e_prio_or     = 2
let e_prio_and    = 3
let e_prio_not    = 4
let e_prio_op1    = 5
let e_prio_op2    = 6
let e_prio_op3    = 7
let e_prio_op4    = 8
let e_prio_uminus = 9

let e_prio_uni   =  5000
let e_prio_excpt = 10000
let e_prio_if3   = 10005

let e_prio_letin = e_prio_base
let e_prio_if    = e_prio_base

let e_prio_max   = Pervasives.max_int

module EP = EcParser 

let lex_single_token name =

  (* Not the fastest solution from the west, but certainly the more
   * robust. TODO: clean-up the operators lexing stuff... *)
  try
    let lexbuf = Lexing.from_string name in
    let token  = EcLexer.main lexbuf in
      match EcLexer.main lexbuf with
      | EP.EOF -> Some token
      | _            -> None
  with EcLexer.LexicalError _ -> None

let priority_of_binop_name name =
  match lex_single_token name with
  | Some (EP.IMPL | EP.IFF)         -> Some (e_prio_impl, `Right)
  | Some EP.OR                      -> Some (e_prio_or, `Right)
  | Some EP.AND                     -> Some (e_prio_and, `Right)
  | Some (EP.EQ | EP.NE | EP.OP1 _) -> Some (e_prio_op1, `Left )
  | Some (EP.OP2 _ | EP.MINUS)      -> Some (e_prio_op2, `Left )
  | Some (EP.OP3 _ | EP.STAR)       -> Some (e_prio_op3, `Left )
  | Some (EP.OP4 _)                 -> Some (e_prio_op4, `Left )
  | _ -> None

let is_uniop name =
  match lex_single_token name with
  | Some EP.MINUS -> Some e_prio_uminus 
  | Some EP.NOT   -> Some e_prio_not 
  | _             -> None 
        
let is_binop name =
  (priority_of_binop_name name) <> None

let maybe_parens prio myprio doc =
  if myprio < prio then Pp.parens doc else doc

(* -------------------------------------------------------------------- *)
let pr_indent (doc : Pp.document) =
  Pp.ifflat doc (Pp.indent 2 doc)

(* -------------------------------------------------------------------- *)
let pr_hang (doc : Pp.document) =
  Pp.hang 2 doc

(* -------------------------------------------------------------------- *)
let pr_seq (doc : Pp.document list) =
  Pp.fold1 (^//^) doc

(* -------------------------------------------------------------------- *)
let pr_vardecl (x,ty) =
  pr_seq [pr_ident x; Pp.colon; pr_type ty] (* FIXME varmap *)

let pr_vardecls d = Pp.parens (pr_list ", " (List.map pr_vardecl d))
(* -------------------------------------------------------------------- *)

let pr_if3 pr_sub prio b e1 e2 = 
  let dc  = pr_sub (e_prio_if3 + 1) b  in 
  let d1  = pr_sub e_prio_base e1 in
  let d2  = pr_sub (e_prio_if3 + 0) e2 in
  let doc = pr_seq [dc; Pp.qmark; d1; Pp.colon; d2] in
  maybe_parens prio e_prio_if3 doc

let pr_if pr_sub prio b e1 e2 = 
  let dc  = pr_sub e_prio_base b  in
  let d1  = pr_sub e_prio_base e1 in
  let d2  = pr_sub e_prio_base e2 in
  let doc = pr_seq [tk_if; dc; tk_then; d1; tk_else; d2] in
  maybe_parens prio e_prio_if doc

let pr_let pr_sub prio pt e1 e2 =
  let dpt =
    match pt with
    | LSymbol x  -> pr_ident x
    | LTuple  xs -> pr_tuple (List.map pr_ident xs)
  in
  let d1  = pr_sub e_prio_base e1 in  (* FIXME: prio *)
  let d2  = pr_sub e_prio_base e2 in
  let doc = pr_seq [tk_let; dpt; Pp.equals; d1; tk_in; d2] in
  maybe_parens prio e_prio_letin doc

let pr_tuple_expr pr_sub es = 
  let docs = List.map (pr_sub (-1)) es in
  Pp.parens (pr_list ", " docs)

let pr_app pr_sub prio op es = 
  let opname = EcIdent.name (EcPath.basename op) in

  let pr_as_std_op () =
    match es with
    | [] -> pr_path op
    | _  ->
        let docs = List.map (pr_sub (-1)) es in
        (pr_path op) ^^ pr_seq [Pp.parens (pr_list "," docs)]
                          
  and try_pr_as_uniop () =
    match es with
    | [e] -> 
        begin match is_uniop opname with
        | None -> None
        | Some(e_prio_uni)  ->
            let doc = !^opname ^^ (pr_sub e_prio_uni e) in 
            Some (maybe_parens prio e_prio_uni doc)
        end

    | _ -> None

  and try_pr_as_binop () =
    match es with
    | [e1; e2] -> 
        begin match priority_of_binop_name opname with
        | None -> None
        | Some (opprio, opassoc) ->
            let (il, ir) =
              match opassoc with
              | `Left  -> (0, 1)
              | `Right -> (1, 0)
            in
            
            let d1  = pr_sub (opprio + il) e1 in
            let d2  = pr_sub (opprio + ir) e2 in
            let doc = pr_seq [d1; !^ opname; d2] in
            Some (maybe_parens prio opprio doc)
        end
          
    | _ -> None
  in
  ofdfl pr_as_std_op
    (List.fpick [try_pr_as_uniop; try_pr_as_binop])

  
let pr_expr (e : tyexpr) =
  let rec pr_expr (prio : int) (e : tyexpr) =
      match e with
      | Evar (x, _) ->
          pr_path x.pv_name

      | Elocal (x, _) ->
          pr_ident x

      | Eint i ->
          Pp.ML.int i
    
      | Eflip ->
          tk_flip
    
      | Eexcepted (e1, e2) ->
          let d1 = pr_expr (e_prio_excpt + 1) e1 in
          let d2 = pr_expr (e_prio_excpt + 0) e2 in
            Pp.parens (pr_seq [d1; Pp.backslash; d2])

      | Ebitstr e ->
          let d = pr_expr e_prio_max e in
            pr_seq [tk_flip; Pp.caret; d]

      | Einter (e1, e2) ->
          let d1 = pr_expr (-1) e1 in
          let d2 = pr_expr (-1) e2 in
            Pp.braces (pr_hang (pr_seq [d1; tk_dotdot; d2]))
  
      | Eif (c, e1, e2) -> pr_if pr_expr prio c e1 e2 

      | Etuple es -> pr_tuple_expr pr_expr es 

      | Eapp (op, es, _) -> pr_app pr_expr prio op es 

      | Elet (pt, e1, e2) -> pr_let pr_expr prio pt e1 e2
 
  in
    pr_expr (-1) e

let pr_form (f : form) =
  let rec pr_form (prio : int) (f:form) =
    match f.f_node with
    | Fquant(q,bd,f) ->
        pr_seq [tk_quant q; pr_vardecls bd; Pp.comma; pr_form prio f ]
    | Fif(b,f1,f2) -> pr_if pr_form prio b f1 f2
    | Flet(lp,f1,f2) -> pr_let pr_form prio lp f1 f2    
    | Fint n -> Pp.ML.int n
    | Flocal id -> pr_ident id
    | Fpvar (x,_,i) -> 
        pr_seq [pr_path x.pv_name; Pp.braces(Pp.ML.int i)]
    | Fapp(p,args) -> pr_app pr_form prio p args
    | Ftuple args -> pr_tuple_expr pr_form args in
   pr_form (-1) f
  

    
    

(* -------------------------------------------------------------------- *)
let pr_dotted (doc : Pp.document) = doc ^^ Pp.dot

(* -------------------------------------------------------------------- *)
let pr_block ~prfx ~pofx (docs : Pp.document list) =
  let docs = List.map pr_indent docs in
  let docs = Pp.fold1 (fun d1 d2 -> d1 ^^ clearbreak ^^ d2) docs in
    prfx ^^ Pp.break1 ^^ docs ^^ Pp.break1 ^^ pofx

(* -------------------------------------------------------------------- *)
let pr_typedecl ((x, tyd) : EcIdent.t * tydecl) =
  let doc = tk_type ^//^ (pr_ident x) in
  let doc =
    match tyd.tyd_type with
    | None    -> doc
    | Some ty -> doc ^//^ Pp.equals ^//^ (pr_type ty)
  in
    pr_dotted (Pp.nest 2 doc)

(* -------------------------------------------------------------------- *)
let pr_dom dom =
  match List.map pr_type dom with
  | []  -> Pp.parens Pp.empty
  | dom -> pr_tuple dom

(* -------------------------------------------------------------------- *)
let pr_sig (dom, codom) =
  (pr_dom dom) ^//^ tk_arrow ^//^ (pr_type codom)

(* -------------------------------------------------------------------- *)
let pr_tyvarsdecl ids = 
  if ids = [] then Pp.empty else Pp.brackets (pr_seq (List.map pr_tvar ids))
  
let pr_opdecl ((x, op) : EcIdent.t * operator) =
  let dop, ddecl = 
    match op.op_kind with
    | OB_oper i -> 
        let dop = if op.op_dom = [] then tk_cnst else tk_op in
        let ddecl = 
          match i.op_def with
          | None -> pr_seq [Pp.colon; pr_sig (op_sig op)]
          | Some (ids, e) -> 
              let vardecls = List.combine ids op.op_dom in
              pr_seq [pr_vardecls vardecls; Pp.colon; pr_type op.op_codom;
                      Pp.equals; pr_expr e] in
        dop, ddecl
    | OB_pred i -> 
        let ddecl = 
          match i.op_def with
          | None -> pr_seq [Pp.colon; pr_dom op.op_dom]
          | Some (ids,_f) -> 
              let vardecls = List.combine ids op.op_dom in
              pr_seq [pr_vardecls vardecls; Pp.equals (* FIXME pp_form f *)]
        in
        tk_pred, ddecl
    | OB_prob _ -> assert false         (* FIXME: no parsing rule *) in
  let doc = pr_seq [dop; pr_ident x; pr_tyvarsdecl op.op_params; ddecl] in
  pr_dotted doc

(* -------------------------------------------------------------------- *)
let pr_axiom ((_x, ax) : EcIdent.t * axiom) =
  let tk =
    match ax.ax_kind with
    | Axiom   -> tk_axiom
    | Lemma _ -> tk_lemma
  in
    tk                                  (* Fails in ecWhy3 *)

(* -------------------------------------------------------------------- *)
let pr_modtype ((x, _tymod) : EcIdent.t * tymod) =
  pr_dotted (pr_seq [tk_module; tk_type; pr_ident x; Pp.equals])

(* -------------------------------------------------------------------- *)
let pr_module (m : module_expr) =
  pr_dotted (pr_seq [tk_module; pr_ident m.me_name; Pp.equals])

(* -------------------------------------------------------------------- *)
let pr_export (p : EcPath.path) =
  pr_dotted (tk_export ^//^ (pr_path p))

(* -------------------------------------------------------------------- *)
let rec pr_ctheory_item (item : ctheory_item) =
  match item with
  | CTh_type     (x, ty) -> pr_typedecl (x, ty)
  | CTh_operator (x, op) -> pr_opdecl   (x, op)
  | CTh_axiom    (x, ax) -> pr_axiom    (x, ax)
  | CTh_modtype  (x, ty) -> pr_modtype  (x, ty)
  | CTh_module   m       -> pr_module   m
  | CTh_theory   (x, th) -> pr_theory   (x, th)
  | CTh_export   p       -> pr_export   p

(* -------------------------------------------------------------------- *)
and pr_theory ((name, ctheory) : EcIdent.t * ctheory) =
  match ctheory.cth_desc with
  | CTh_clone p ->
      tk_clone ^//^ (pr_path p) ^//^ tk_as ^//^ (pr_ident name)

  | CTh_struct cstruct ->
      let pr_cstruct = List.map pr_ctheory_item cstruct in
        pr_block
          ~prfx:(pr_dotted (tk_theory ^//^ (pr_ident name)))
          ~pofx:(pr_dotted (tk_end    ^//^ (pr_ident name)))
          pr_cstruct

(* -------------------------------------------------------------------- *)
let pretty (doc : Pp.document) =
  Format.fprintf Format.err_formatter "%a@?"
    (Pp.Formatter.pretty 0.8 78) doc

(** {1 PP-style printers} *)

(* -------------------------------------------------------------------- *)
let (~$) = format_of_string

(* -------------------------------------------------------------------- *)
let pp_located loc pp_elt fmt x =
  Format.fprintf fmt "%s: %a" (Location.tostring loc) pp_elt x

(* -------------------------------------------------------------------- *)
let rec pp_qsymbol fmt = function
  | ([]    , x) -> Format.fprintf fmt "%s" x
  | (n :: p, x) -> Format.fprintf fmt "%s.%a" n pp_qsymbol (p, x)

(* -------------------------------------------------------------------- *)
let rec pp_path fmt = function
  | EcPath.Pident x      -> Format.fprintf fmt "%s" (EcIdent.name x)
  | EcPath.Pqname (p, x) -> Format.fprintf fmt "%a.%s" pp_path p (EcIdent.name x)

(* -------------------------------------------------------------------- *)
let pp_of_pr (pr : 'a pr) (fmt : Format.formatter) (x : 'a) =
  Format.fprintf fmt "%a" (Pp.Formatter.pretty 0.8 78) (pr x)

(* -------------------------------------------------------------------- *)
let pp_type     = fun ?vmap -> pp_of_pr (pr_type ?vmap)
let pp_dom      = pp_of_pr pr_dom
let pp_typedecl = pp_of_pr pr_typedecl
let pp_opdecl   = pp_of_pr pr_opdecl
let pp_axiom    = pp_of_pr pr_axiom
let pp_modtype  = pp_of_pr pr_modtype
let pp_module   = pp_of_pr pr_module
let pp_export   = pp_of_pr pr_export
let pp_theory   = pp_of_pr pr_theory
