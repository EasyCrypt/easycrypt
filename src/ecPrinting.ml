(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcFormat
open EcTypes
open EcFol
open EcTypesmod
open EcTheory
open EcDecl
open EcParsetree
open EcEnv

module NameGen = EcUidgen.NameGen
module Mid     = EcIdent.Mid

(* -------------------------------------------------------------------- *)
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
let pp_of_pr (pr : 'a pr) (fmt : Format.formatter) (x : 'a) =
  Format.fprintf fmt "%a" (Pp.Formatter.pretty 0.8 78) (pr x)

(* -------------------------------------------------------------------- *)
module type IPrettyPrinter = sig
  type t                                (* ident-2-path *)
  val init : EcEnv.env * EcEnv.env list -> t
  val mono : EcEnv.env -> t

  (* ------------------------------------------------------------------ *)
  val pr_type     : t -> ?vmap:NameGen.t -> ty pr
  val pr_expr     : t -> tyexpr pr
  val pr_form     : t -> EcFol.form pr
  val pr_dom      : t -> EcTypes.dom pr
  val pr_typedecl : t -> (EcPath.path * tydecl     ) pr
  val pr_opdecl   : t -> (EcPath.path * operator   ) pr
  val pr_axiom    : t -> (EcPath.path * axiom      ) pr
  val pr_modsig   : t -> (EcPath.path * module_sig ) pr
  val pr_module   : t -> (EcPath.path * module_expr) pr
  val pr_theory   : t -> (EcPath.path * ctheory    ) pr
  val pr_export   : t -> EcPath.path pr
  val pr_lgoal    : t -> (EcFol.hyps * EcFol.form) pr

  (* ------------------------------------------------------------------ *)
  val pp_type     : t -> ?vmap:NameGen.t -> ty pp
  val pp_expr     : t -> tyexpr pp
  val pp_form     : t -> EcFol.form pp
  val pp_dom      : t -> EcTypes.dom pp
  val pp_typedecl : t -> (EcPath.path * tydecl     ) pp
  val pp_opdecl   : t -> (EcPath.path * operator   ) pp
  val pp_axiom    : t -> (EcPath.path * axiom      ) pp
  val pp_modsig   : t -> (EcPath.path * module_sig ) pp
  val pp_module   : t -> (EcPath.path * module_expr) pp
  val pp_theory   : t -> (EcPath.path * ctheory    ) pp
  val pp_export   : t -> EcPath.path pp
  val pp_lgoal    : t -> (EcFol.hyps * EcFol.form) pp
end

(* -------------------------------------------------------------------- *)
module type IIdentPrinter = sig
  type t
  val init : (EcEnv.env * EcEnv.env list) -> t 

  val add_ty    : t -> EcPath.path -> t
  val add_local : t -> EcIdent.t   -> t
  val add_pvar  : t -> EcPath.path -> t
  val add_fun   : t -> EcPath.path -> t
  val add_mod   : t -> EcPath.path -> t
  val add_modty : t -> EcPath.path -> t
  val add_op    : t -> EcPath.path -> t
  val add_ax    : t -> EcPath.path -> t
  val add_th    : t -> EcPath.path -> t

  val string_of_ident : EcIdent.t -> string

  val tv_symb    : t -> EcIdent.t    -> EcSymbols.symbol
  val ty_symb    : t -> EcPath.path  -> EcSymbols.qsymbol
  val local_symb : t -> EcIdent.t    -> EcSymbols.symbol
  val pv_symb    : t -> EcPath.mpath -> int option -> EcSymbols.qsymbol
  val fun_symb   : t -> EcPath.mpath -> EcSymbols.qsymbol
  val mod_symb   : t -> EcPath.mpath -> EcSymbols.qsymbol
  val modty_symb : t -> EcPath.path  -> EcSymbols.qsymbol
  val op_symb    : 
      t -> EcPath.path -> ty list -> ty list option -> EcSymbols.qsymbol
  val ax_symb    : t -> EcPath.path  -> EcSymbols.qsymbol
  val th_symb    : t -> EcPath.path  -> EcSymbols.qsymbol
end

(* -------------------------------------------------------------------- *)
let tk_tvars  = !^ "type variables"
let tk_goalline = 
!^ "-------------------------------------------------------------------" 
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
let tk_from_int = !^ "%r"
let tk_forall = !^ "forall"
let tk_fun    = !^ "fun"
let tk_if     = !^ "if"
let tk_in     = !^ "in"
let tk_lemma  = !^ "lemma"
let tk_let    = !^ "let"
let tk_module = !^ "module"
let tk_op     = !^ "op"
let tk_pred   = !^ "pred"
let tk_then   = !^ "then"
let tk_theory = !^ "theory"
let tk_type   = !^ "type"
let tk_var    = !^ "var"
let tk_while  = !^ "while"
let tk_with   = !^ "with"

let tk_arrow  = !^ "->"
let tk_larrow  = !^ "<-"
let tk_dotdot = !^ ".."
let tk_pipe   = !^ "|"
let tk_dlbracket = !^ ".["
let tk_lbracket = !^ "["
let tk_rbracket = !^ "]"

(* -------------------------------------------------------------------- *)
module MakePP(M : IIdentPrinter) :
  IPrettyPrinter with type t = M.t
=
struct
  module EP = EcParser

  (* ------------------------------------------------------------------ *)
  type t = M.t
  let init = M.init
  let mono env = M.init(env,[])
  (* ------------------------------------------------------------------ *)
  let pr_symbol (x : symbol) = !^x

  (* ------------------------------------------------------------------ *)
  let pr_qsymbol ((p, x) : qsymbol) =
    !^ (String.concat "." (p @ [x]))

  let pr_ident _ id = !^ (M.string_of_ident id)

  (* ------------------------------------------------------------------ *)
  let pr_tv_symb (tenv : t) (x : EcIdent.t) =
    pr_symbol (M.tv_symb tenv x)

  (* ------------------------------------------------------------------ *)
  let pr_ty_symb (tenv : t) (p : EcPath.path) =
    pr_qsymbol (M.ty_symb tenv p)

  (* ------------------------------------------------------------------ *)
  let pr_local_symb (tenv : t) (x : EcIdent.t) =
    pr_symbol (M.local_symb tenv x)

  (* ------------------------------------------------------------------ *)
  let pr_pv_symb (tenv : t) (p : EcPath.mpath) (io : int option) =
    pr_qsymbol (M.pv_symb tenv p io)

  (* ------------------------------------------------------------------ *)
  let pr_fun_name (tenv : t) (p :EcPath.mpath) =
    pr_qsymbol (M.fun_symb tenv p)

  (* ------------------------------------------------------------------ *)
  let pr_mod_name (tenv : t) (p : EcPath.mpath) =
    pr_qsymbol (M.mod_symb tenv p)

  (* ------------------------------------------------------------------ *)
  let pr_modty_symb (tenv : t) (p : EcPath.path) =
    pr_qsymbol (M.modty_symb tenv p)

  (* ------------------------------------------------------------------ *)
  let pr_ax_name (tenv : t) (p : EcPath.path) =
    pr_qsymbol (M.ax_symb tenv p)

  (* ------------------------------------------------------------------ *)
  let pr_th_name (tenv : t) (p : EcPath.path) =
    pr_qsymbol (M.th_symb tenv p)

  (* ------------------------------------------------------------------ *)
  let pr_tvar (tenv : t) (id : EcIdent.t) =
    pr_symbol (M.tv_symb tenv id)

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
    let rec pr_type btuple ty = 
      match ty.ty_node with 
      | Tvar id ->
          pr_tvar tenv id

      | Tunivar id ->
          pr_tunivar uidmap id

      | Ttuple tys ->
          let doc = pr_list_map (pr_type true) " * " tys in (* FIXME "*" *)
          if btuple then Pp.parens doc else doc

      | Tconstr (name, tyargs) -> 
          let nd = pr_ty_symb tenv name in
          begin match tyargs with
          | [] -> nd
          | [ty] -> pr_type true ty ^//^ nd
          | _  -> (pr_tuple (List.map (pr_type false) tyargs)) ^//^ nd
          end
      | Tfun(t1,t2) ->
          let doc = 
            pr_type true t1 ^^ tk_arrow ^//^ pr_type false t2 in (* FIXME prio *)
          if btuple then Pp.parens doc else doc
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
  let appprio           = (10000, `Infix `NonAssoc) (* ??? FIXME *)
  let e_get_prio        = (20000, `Infix `Left)     (* ??? FIXME *)

  let min_op_prec = (-1     , `Infix `NonAssoc)
  let max_op_prec = (max_int, `Infix `NonAssoc)

  (* ------------------------------------------------------------------ *)
  let is_ident_symbol name = 
    match EcIo.lex_single_token name with
    | Some EP.IDENT _ -> true
    | _ -> false

  let priority_of_binop_name name =
    match EcIo.lex_single_token name with
    | Some EP.IMPL  -> Some e_bin_prio_impl
    | Some EP.IFF   -> Some e_bin_prio_impl
    | Some(EP.OR _) -> Some e_bin_prio_or
    | Some(EP.AND _)-> Some e_bin_prio_and
    | Some EP.EQ    -> Some e_bin_prio_eq
    | Some EP.NE    -> Some e_bin_prio_eq
    | Some EP.GT    -> Some e_bin_prio_op1
    | Some EP.OP1 _ -> Some e_bin_prio_op1
    | Some EP.OP2 _ -> Some e_bin_prio_op2
    | Some EP.OP3 _ -> Some e_bin_prio_op3
    | Some EP.STAR  -> Some e_bin_prio_op3
    | Some EP.OP4 _ -> Some e_bin_prio_op4

    | _ -> None

  (* ------------------------------------------------------------------ *)
  let priority_of_uniop name =
    match EcIo.lex_single_token name with
    | Some EP.NOT   -> Some e_uni_prio_not
    | Some EP.EQ    -> Some e_uni_prio_uminus
    | Some(EP.AND _)-> Some e_uni_prio_uminus  
    | Some(EP.OR _) -> Some e_uni_prio_uminus  
    | Some EP.STAR  -> Some e_uni_prio_uminus  
    | Some EP.GT    -> Some e_uni_prio_uminus  
    | Some EP.OP1 _ -> Some e_uni_prio_uminus 
    | Some EP.OP2 _ -> Some e_uni_prio_uminus
    | Some EP.OP3 _ -> Some e_uni_prio_uminus
    | Some EP.OP4 _ -> Some e_uni_prio_uminus
    | _             -> None

  (* ------------------------------------------------------------------ *)
  let is_binop name =
    (priority_of_binop_name name) <> None

  (* ------------------------------------------------------------------ *)
  let pr_vardecl (tenv : t) (x, ty) =
    let tenv1 = M.add_local tenv x in
    tenv1, pr_seq [pr_local_symb tenv1 x; Pp.colon; pr_type tenv ty]

  (* ------------------------------------------------------------------ *)
  let pr_vardecls (tenv : t) d =
    let tenv, ds = List.map_fold pr_vardecl tenv d in
    tenv, Pp.parens (pr_list ", " ds)

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
    let ids = ids_of_lpattern pt in
    let subtenv = List.fold_left M.add_local tenv ids in

    let dpt = pr_tuple (List.map (pr_local_symb subtenv) ids) in

    let d1  = pr_sub tenv (e_bin_prio_letin, `NonAssoc) e1 in
    let d2  = pr_sub subtenv (e_bin_prio_letin, `NonAssoc) e2 in
    let doc = pr_seq [tk_let; dpt; Pp.equals; d1; tk_in; d2] in
    bracket outer e_bin_prio_letin doc

  (* ------------------------------------------------------------------ *)
  let pr_tuple_expr (tenv : t) pr_sub es =
    let docs = List.map (pr_sub tenv (min_op_prec, `NonAssoc)) es in
    Pp.parens (pr_list ", " docs)

  (* ------------------------------------------------------------------ *)

  let pr_op_name_qs (qs,s) =
    if is_ident_symbol s then pr_qsymbol (qs,s)
    else match List.rev qs with
    | [] -> !^"[" ^^ !^s ^^ !^"]"
    | s'::tl ->
        let qs' = List.rev tl in
        pr_qsymbol (qs',s') ^^ !^".[" ^^ !^ s ^^ !^"]"

  let pr_op_name (tenv : t) (p : EcPath.path) tvi esig =
    pr_op_name_qs (M.op_symb tenv p tvi esig)

  let pr_app get_ty (tenv : t) pr_sub outer op tvi es =
     (* FIXME : special notations list,  sampling {0,1} {0,1}^k [k1..k2] ....
     *)

    let esig = try Some (List.map get_ty es) with _ -> None in

    let qs,opname = M.op_symb tenv op tvi esig in
    
    let pr_as_std_op () =
      let docs,prio = 
        (* FIXME, priority *)
        if qs = [] then
          match opname, es with
          | "__nil", [] -> [tk_lbracket ^^ tk_rbracket], max_op_prec
          | "__abs", [e] -> 
              [ tk_pipe; pr_sub tenv  (min_op_prec, `NonAssoc) e; tk_pipe ],
              appprio 
          | "__get", [e1;e2] ->
             [ pr_sub tenv (e_get_prio, `Left) e1 ^^
               tk_dlbracket ^^
               pr_sub tenv (min_op_prec, `NonAssoc) e2 ^^
               tk_rbracket ], 
              e_get_prio
          | "__set", [e1;e2;e3] ->
              [ pr_sub tenv (e_get_prio, `Left) e1 ^^
                tk_dlbracket ^^
                pr_sub tenv (min_op_prec, `NonAssoc) e2;
                tk_larrow;
                pr_sub tenv (min_op_prec, `NonAssoc) e3 ^^
                tk_rbracket ], 
              e_get_prio
          | _ ->
              pr_op_name_qs (qs,opname) :: 
              List.map (pr_sub tenv (appprio, `Right)) es, 
              appprio
        else 
          pr_op_name_qs (qs,opname) :: 
          List.map (pr_sub tenv (appprio, `Right)) es, appprio in
      bracket outer prio (pr_seq docs) in

    let try_pr_as_uniop () =
      if qs = [] then
        match es with
        | [e] ->
            begin match priority_of_uniop opname with
            | None -> None
            | Some opprio  ->
                let opprio = (opprio, `Prefix) in
                let doc =
                  !^ opname ^^ (pr_sub tenv (opprio, `NonAssoc) e)
                in
                Some (bracket outer opprio doc)
            end
        | _ -> None
      else None

    and try_pr_as_binop () =
      if qs = [] then
        match es with
        | [e1; e2] ->
            begin match priority_of_binop_name opname with
            | None -> None
            | Some opprio ->
                let d1  = pr_sub tenv (opprio, `Left ) e1 in
                let d2  = pr_sub tenv (opprio, `Right) e2 in
                let doc = pr_seq [d1; !^ opname ; d2] in
                Some (bracket outer opprio doc)
            end
        | _ -> None
      else None
          
    and try_pr_special () = 
      let qs = EcPath.toqsymbol op in
      match es with
      | [] when qs = EcCoreLib.s_dbool -> Some tk_flip
      | [e] when qs = EcCoreLib.s_dbitstring ->
          Some (tk_flip ^^ !^"^" ^^ pr_sub tenv (max_op_prec, `NonAssoc) e)
      | [e] when qs = EcCoreLib.s_from_int ->
          Some ( pr_sub tenv (max_op_prec, `NonAssoc) e ^^ tk_from_int)
      | [e1;e2] when qs = EcCoreLib.s_dinter ->
          Some (tk_lbracket ^^ 
                pr_sub tenv (min_op_prec, `NonAssoc) e1 ^^
                tk_dotdot ^^
                pr_sub tenv (min_op_prec, `NonAssoc) e2 ^^
                tk_rbracket)
      | _ -> None

    in
      ofdfl pr_as_std_op
        (List.fpick [try_pr_special;try_pr_as_uniop; try_pr_as_binop])

  (* ------------------------------------------------------------------ *)
  let pr_expr (tenv : t) (e : tyexpr) =
    let rec pr_expr (tenv : t) outer (e : tyexpr) =
        match e.tye_desc with
        | Evar x ->
            pr_pv_symb tenv x.pv_name None

        | Elocal x ->
            pr_local_symb tenv x

        | Eop(op,tys) -> (* FIXME infix, prefix, ty_inst *)
            pr_op_name tenv op tys (Some [])

        | Eint i ->
            Pp.ML.int i

        | Eif (c, e1, e2) ->
            pr_if tenv pr_expr outer c e1 e2

        | Etuple es ->
            pr_tuple_expr tenv pr_expr es

        | Eapp({tye_desc = Eop(op,tys) }, args) -> 
            pr_app e_ty tenv pr_expr outer op tys args

        | Eapp (e, args) -> 
            let docs = List.map (pr_expr tenv (min_op_prec, `NonAssoc)) args in
            (pr_expr tenv (max_op_prec, `NonAssoc) e) ^^ 
            pr_seq [Pp.parens (pr_list "," docs)]

        | Elet (pt, e1, e2) ->
            pr_let tenv pr_expr outer pt e1 e2

    in
      pr_expr tenv (min_op_prec, `NonAssoc) e

  (* ------------------------------------------------------------------ *)
  let tk_quant = function
    | Lforall -> tk_forall
    | Lexists -> tk_exists






  (* MODULE PPRINTING *)




  (* ------------------------------------------------------------------ *)
  let pr_local (tenv : t) (x : EcIdent.t) (ty : ty) =
    (* assert false (\* FIXME *\) *)
   pr_seq [!^"var"; pr_ident tenv x; Pp.colon; pr_type tenv ty] ^^ Pp.semi



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
  let pr_lvalue (tenv : t) (lv : lvalue) =
    match lv with
    | LvVar (p, _) ->
        pr_pv_symb tenv p.pv_name None

    | LvTuple ps ->
        let pr (p,_) = pr_pv_symb tenv p.pv_name None in
        let docs = List.map pr ps in
        Pp.parens (pr_list "," docs)

    | LvMap (_,x,e,_) ->
        pr_pv_symb tenv x.pv_name None ^^ !^"[" ^^ pr_expr tenv e ^^ !^"]"

  (* ------------------------------------------------------------------ *)
  let pr_instr (tenv : t) (i : instr) =
    let doc =
      match i with
      | Sasgn (lv, e) ->
          pr_seq [pr_lvalue tenv lv; Pp.equals; pr_expr tenv e]
      | Srnd (lv, e) ->
          pr_seq [pr_lvalue tenv lv; Pp.equals; Pp.dollar; pr_expr tenv e]

      | Scall (lv, p, args) -> begin
          let doc =
               (pr_fun_name tenv p)
            ^^ Pp.parens (pr_list_map (pr_expr tenv) "," args)
          in
            match lv with
            | None    -> doc
            | Some lv -> pr_seq [pr_lvalue tenv lv; Pp.equals; doc]
      end

      | Sassert e ->
          pr_seq [tk_assert; Pp.parens (pr_expr tenv e)]

      | Sif (e, _b1, _b2) ->
          pr_seq [tk_if; Pp.parens (pr_expr tenv e)]

      | Swhile (e, _body) ->
          pr_seq [tk_while; Pp.parens (pr_expr tenv e)]

    in
      doc ^^ Pp.semi

  (* ------------------------------------------------------------------ *)
  let rec pr_module_item (scope : EcPath.path) (tenv : t) (item : module_item) =
    let xpath x = EcPath.pqname (scope, x) in

      match item with
      | MI_Variable v ->
          let doc = pr_modvar tenv (xpath v.v_name, v) in
            (M.add_pvar tenv (xpath v.v_name), doc)

      | MI_Function f ->
          let doc = pr_modfun tenv (xpath f.f_name, f) in
            (M.add_fun tenv (xpath f.f_name), doc)

      | MI_Module me ->
          let doc = pr_module tenv (xpath me.me_name, me) in
            (M.add_mod tenv (xpath me.me_name), doc)

  (* ------------------------------------------------------------------ *)
  and pr_modvar (tenv : t) ((_, v) : EcPath.path * variable) =
    pr_seq [tk_var; pr_symbol v.v_name; Pp.colon; pr_type tenv v.v_type]

  (* ------------------------------------------------------------------ *)
  and pr_modfun (tenv : t) ((_, f) : EcPath.path * function_) =
    let fname = f.f_sig.fs_name in
    let fparams, fres = f.f_sig.fs_sig in

    let dparams =
      List.map
        (fun (x, ty) -> pr_seq [pr_symbol x; Pp.colon; pr_type tenv ty])
        fparams in
    let dparams = Pp.parens (pr_list "," dparams) in

    let prelude =
      pr_seq [tk_fun; !^fname ^^ dparams; Pp.colon; pr_type tenv fres]
    in

      match f.f_def with
      | None ->
          prelude

      | Some def ->
          let dlocals =
            List.map
              (fun (x, ty) -> pr_local tenv (EcIdent.create x) ty)
              def.f_locals

          and dbody =
            let bodytenv =
              List.fold_left
                (fun tenv x -> M.add_local tenv (EcIdent.create x))
                tenv
                (List.map fst ((fst f.f_sig.fs_sig) @ def.f_locals))
            in
              List.map (pr_instr bodytenv) def.f_body
          in
            (pr_seq [prelude; Pp.equals]) ^/^ (pr_mblocks [dlocals; dbody])

  (* ------------------------------------------------------------------ *)
  and pr_module (tenv : t) ((p, m) : EcPath.path * module_expr) =
    let mename  = m.me_name in
    let prelude = pr_seq [tk_module; pr_symbol mename] in
    let moddoc  =

      match m.me_body with
      | ME_Alias m -> 
          pr_seq [prelude; Pp.equals; !^ (EcPath.m_tostring m)]

      | ME_Decl _modty ->
          assert false                  (* FIXME *)

      | ME_Structure mstruct ->
          let _, bodydoc =
            List.map_fold (pr_module_item p) tenv mstruct.ms_body
          in
                (pr_seq [prelude; Pp.equals])
            ^/^ (pr_block Pp.lbrace Pp.rbrace bodydoc)
    in
      pr_dotted moddoc

  (* ------------------------------------------------------------------ *)
  let pr_typedecl (tenv : t) ((x, tyd) : EcPath.path * tydecl) =
    let basename = EcPath.basename x in
    let dparams =
      match tyd.tyd_params with
      | [] -> Pp.empty
      | _  -> Pp.parens (pr_list_map (pr_tvar tenv) ", " tyd.tyd_params)
    in

    let doc = tk_type ^//^ dparams ^^ (pr_symbol basename) in
    let doc =
      match tyd.tyd_type with
      | None    -> doc
      | Some ty -> doc ^//^ Pp.equals ^//^ (pr_type tenv ty)
    in
      pr_dotted (Pp.nest 2 doc)









  (* ------------------------------------------------------------------ *)
  let pr_form (tenv : t) (f : form) =
    let rec pr_form (tenv : t) outer (f : form) =
      match f.f_node with
      | Fint n ->
          Pp.ML.int n

      | Flocal id ->
          pr_local_symb tenv id

      | Fpvar (x, i) ->
          pr_seq [pr_pv_symb tenv x.pv_name (Some i); Pp.braces (Pp.ML.int i)]

      | Fquant (q, bd, f) ->
          let subtenv, dd = pr_vardecls tenv bd in 
          pr_seq [tk_quant q;
                  dd^^Pp.comma;
                  pr_form subtenv outer f]

      | Fif (b, f1, f2) ->
          pr_if tenv pr_form outer b f1 f2

      | Flet (lp, f1, f2) ->
          pr_let tenv pr_form outer lp f1 f2

      | Fop(op,tvi) -> (* FIXME infix, prefix, ty_inst *)
            pr_op_name tenv op tvi (Some [])

      | Fapp ({f_node = Fop(p,tys)}, args) ->
          pr_app EcFol.ty tenv pr_form outer p tys args

      | Fapp (e,args) ->
          let docs = List.map (pr_form tenv (min_op_prec, `NonAssoc)) args in
          (pr_form tenv (max_op_prec, `NonAssoc) e) ^^ 
          pr_seq [Pp.parens (pr_list "," docs)]

      | Ftuple args ->
          pr_tuple_expr tenv pr_form args
            
      | Fhoare(pre,def,post) -> 
        (* copy pasted from pr_modfun, code repetition *)
          let dlocals =
            List.map
              (fun (x, ty) -> pr_local tenv (EcIdent.create x) ty)
              def.f_locals

          and dbody =
            let bodytenv =
              List.fold_left
                (fun tenv x -> M.add_local tenv (EcIdent.create x))
                tenv
                (List.map fst (def.f_locals))
            in
              List.map (pr_instr bodytenv) def.f_body
          in
        (* end of copy pasted *)

        pr_seq [ Pp.braces (pr_form tenv outer pre);
                 pr_mblocks [dlocals; dbody];
                 Pp.braces (pr_form tenv outer post) ]

    in
      pr_form tenv (min_op_prec, `NonAssoc) f

















  (* ------------------------------------------------------------------ *)
  let pr_opdecl (tenv : t) ((x, op) : EcPath.path * operator) =
    let basename = EcPath.basename x in

    let dop, ddecl =
      match op.op_kind with
      | OB_oper i ->
          let dop = if op.op_dom = [] then tk_cnst else tk_op in
          let ddecl =
            match i with
            | None -> pr_seq [Pp.colon; pr_sig tenv (op_sig op)]
            | Some (ids, e) ->
                let vardecls = List.combine ids op.op_dom in
                let subtenv, dd = pr_vardecls tenv vardecls in
                pr_seq [dd;
                        Pp.colon;
                        pr_type tenv op.op_codom;
                        Pp.equals;
                        pr_expr subtenv e]
          in
            (dop, ddecl)

      | OB_pred i ->
          let ddecl =
            match i with
            | None -> pr_seq [Pp.colon; pr_dom tenv op.op_dom]
            | Some (ids,f) ->
                let vardecls = List.combine ids op.op_dom in
                let subtenv, dd = pr_vardecls tenv vardecls in
                pr_seq [dd; Pp.equals; pr_form subtenv f]
          in
          tk_pred, ddecl in

    let doc =
      pr_seq [dop; pr_symbol basename;
              pr_tyvarsdecl tenv op.op_params; ddecl]
    in
      pr_dotted doc

  (* ------------------------------------------------------------------ *)
  let pr_axiom (tenv : t) ((x, ax) : EcPath.path * axiom) =
    let basename = EcPath.basename x in

    let tk =
      match ax.ax_kind with
      | Axiom   -> tk_axiom
      | Lemma _ -> tk_lemma

    and pr_name =
      match ax.ax_params with
      | [] -> pr_symbol basename
      | _  ->    (pr_symbol basename)
              ^^ (Pp.angles (pr_list_map (pr_ident tenv) "," ax.ax_params))

    and spec =
      match ax.ax_spec with
      | None   -> !^"<why3-imported>"
      | Some f -> pr_form tenv f
    in

      pr_dotted (pr_seq [tk; pr_name; Pp.colon; spec])

  (* ------------------------------------------------------------------ *)
  let pr_modsig (_tenv : t) ((x, _tymod) : EcPath.path * module_sig) =
    let basename = EcPath.basename x in
      pr_dotted (pr_seq [tk_module; tk_type; pr_symbol basename; Pp.equals])

  (* ------------------------------------------------------------------ *)
  let pr_export (tenv : t) (p : EcPath.path) =
    pr_dotted (tk_export ^//^ (pr_th_name tenv p))

  (* ------------------------------------------------------------------ *)
  let rec pr_ctheory_item (scope : EcPath.path) (tenv : t) (item : ctheory_item) =
    let xpath x = EcPath.pqname (scope, x) in

    match item with
    | CTh_type (x, ty) ->
        let doc = pr_typedecl tenv (xpath x, ty) in
          (M.add_ty tenv (xpath x), doc)

    | CTh_operator (x, op) ->
        let doc = pr_opdecl tenv (xpath x, op) in
          (M.add_op tenv (xpath x), doc)

    | CTh_axiom (x, ax) ->
        let doc = pr_axiom tenv (xpath x, ax) in
          (M.add_ax tenv (xpath x), doc)

    | CTh_modtype (x, ty) ->
        let doc = pr_modsig tenv (xpath x, ty) in
          (M.add_modty tenv (xpath x), doc)

    | CTh_module m ->
        let doc = pr_module tenv (xpath m.me_name, m) in
          (M.add_mod tenv (xpath m.me_name), doc)

    | CTh_theory (x, th) ->
        let doc = pr_theory tenv (xpath x, th) in
          (M.add_th tenv (xpath x), doc)

    | CTh_export p ->
        (tenv, pr_export tenv p)

  (* ------------------------------------------------------------------ *)
  and pr_theory (tenv : t) ((name, ctheory) : EcPath.path * ctheory) =
    let pr_ext ((x, e) : EcIdent.t * ctheory_override) =
      match e with
      | CTHO_Type ty ->
          pr_seq [tk_type; pr_ident tenv x; Pp.equals; pr_type tenv ty]

      | CTHO_Module (mp, margs) -> begin
          let doc =
              match margs with
              | [] -> pr_th_name tenv mp
              | _  -> pr_seq [
                  pr_th_name tenv mp;
                  Pp.parens (pr_list_map (pr_th_name tenv) "," margs)]
          in
            pr_seq [tk_module; pr_ident tenv x; Pp.equals; doc]
      end
    in
      match ctheory.cth_desc with
      | CTh_clone p ->
          let doc = [tk_clone; pr_th_name tenv p.cthc_base] in
          let doc =
            let name1 = EcPath.basename name
            and name2 = EcPath.basename p.cthc_base in
              match name1 = name2 with
              | true  -> doc
              | false -> doc @ [tk_as; pr_symbol (EcPath.basename name)] in
          let doc =
            match p.cthc_ext with
            | [] -> doc
            | _  ->
              let pext = List.map pr_ext p.cthc_ext in
              let pext = [tk_with; (pr_list ", " pext)] in
                doc @ pext
          in
            pr_seq doc
  
      | CTh_struct cstruct ->
          let basename = EcPath.basename name in
          let _, pr_cstruct =
            List.map_fold (pr_ctheory_item name) tenv cstruct
          in
            pr_block
              ~prfx:(pr_dotted (tk_theory ^//^ (pr_symbol basename)))
              ~pofx:(pr_dotted (tk_end    ^//^ (pr_symbol basename)))
              pr_cstruct

  let pr_hyp (t,d) (id,k) = 
    let dk = 
      match k with
      | LD_var (ty, _body) -> pr_type t ty (* FIXME body *)
      | LD_hyp f           -> pr_form t f in
    let dh = pr_ident t id ^^ (!^ " : ") ^//^ dk in
    (M.add_local t id, d^/^dh)   

  let pr_lgoal t (hyps,concl) = 
    let doc = 
      tk_tvars ^^ (!^ " : ") ^//^ pr_list_map (pr_tvar t) ", " hyps.h_tvar in
    let (t,doc) = List.fold_left pr_hyp (t,doc) (List.rev hyps.h_local) in
    let doc = doc ^/^ tk_goalline in
    (!^ "Current goal") ^@^ doc ^/^ pr_form t concl ^^ clearbreak

  (* ------------------------------------------------------------------ *)
  let pp_type     = fun t ?vmap -> pp_of_pr (pr_type t ?vmap)
  let pp_dom      = fun t -> pp_of_pr (pr_dom t)
  let pp_typedecl = fun t -> pp_of_pr (pr_typedecl t)
  let pp_opdecl   = fun t -> pp_of_pr (pr_opdecl t)
  let pp_axiom    = fun t -> pp_of_pr (pr_axiom t)
  let pp_modsig   = fun t -> pp_of_pr (pr_modsig t)
  let pp_module   = fun t -> pp_of_pr (pr_module t)
  let pp_export   = fun t -> pp_of_pr (pr_export t)
  let pp_theory   = fun t -> pp_of_pr (pr_theory t)
  let pp_expr     = fun t -> pp_of_pr (pr_expr t)
  let pp_form     = fun t -> pp_of_pr (pr_form t)
  let pp_lgoal    = fun t -> pp_of_pr (pr_lgoal t)
end

(* -------------------------------------------------------------------- *)
module RawIdentPrinter : IIdentPrinter with type t = unit =
struct
  type t = unit
  let init _ = ()

  let add_ty    = fun (_ : t) (_ : EcPath.path) -> ()
  let add_local = fun (_ : t) (_ : EcIdent.t  ) -> ()
  let add_pvar  = fun (_ : t) (_ : EcPath.path) -> ()
  let add_fun   = fun (_ : t) (_ : EcPath.path) -> ()
  let add_mod   = fun (_ : t) (_ : EcPath.path) -> ()
  let add_modty = fun (_ : t) (_ : EcPath.path) -> ()
  let add_op    = fun (_ : t) (_ : EcPath.path) -> ()
  let add_ax    = fun (_ : t) (_ : EcPath.path) -> ()
  let add_th    = fun (_ : t) (_ : EcPath.path) -> ()

  let symb_of_ident (x : EcIdent.t) =
    ([], EcIdent.tostring x)

  let symb_of_path (p : EcPath.path) =
    ([], EcPath.basename p)

  let symb_of_mpath (p : EcPath.mpath) = symb_of_path (EcPath.path_of_mpath p)

  let string_of_ident = EcIdent.tostring 

  let tv_symb    = fun (_ : t) (x : EcIdent.t  )      -> EcIdent.tostring x
  let ty_symb    = fun (_ : t) (p : EcPath.path)      -> symb_of_path p
  let local_symb = fun (_ : t) (x : EcIdent.t  )      -> EcIdent.tostring x
  let pv_symb    = fun (_ : t) (p : EcPath.mpath) _   -> symb_of_mpath p
  let fun_symb   = fun (_ : t) (p : EcPath.mpath)     -> symb_of_mpath p
  let mod_symb   = fun (_ : t) (p : EcPath.mpath)     -> symb_of_mpath p
  let modty_symb = fun (_ : t) (p : EcPath.path)      -> symb_of_path p
  let op_symb    = fun (_ : t) (p : EcPath.path) _ _  -> symb_of_path p
  let ax_symb    = fun (_ : t) (p : EcPath.path)      -> symb_of_path p
  let th_symb    = fun (_ : t) (p : EcPath.path)      -> symb_of_path p
end

(* -------------------------------------------------------------------- *)
(*module LongRawIdentPrinter : IIdentPrinter with type t = unit =
struct
  type t = unit
  let init _ = ()

  let add_ty    = fun (_ : t) (_ : EcPath.path) -> ()
  let add_local = fun (_ : t) (_ : EcIdent.t  ) -> ()
  let add_pvar  = fun (_ : t) (_ : EcPath.path) -> ()
  let add_fun   = fun (_ : t) (_ : EcPath.path) -> ()
  let add_mod   = fun (_ : t) (_ : EcPath.path) -> ()
  let add_modty = fun (_ : t) (_ : EcPath.path) -> ()
  let add_op    = fun (_ : t) (_ : EcPath.path) -> ()
  let add_ax    = fun (_ : t) (_ : EcPath.path) -> ()
  let add_th    = fun (_ : t) (_ : EcPath.path) -> ()

  let symb_of_ident (x : EcIdent.t) =
    ([], EcIdent.tostring x)

  let symb_of_path (p : EcPath.path) =
    match List.rev (EcPath.tolist p) with
    | x :: qn -> (List.rev qn, x)
    | [] -> assert false

  let symb_of_epath (p : EcPath.epath) =
    match p with
    | EcPath.EPath p -> symb_of_path p
    | EcPath.EModule (mid, None) -> ([], EcIdent.tostring mid)
    | EcPath.EModule (mid, Some x) -> ([EcIdent.tostring mid], x)

  let symb_of_cref (p : EcPath.cref) =
    match p with
    | EcPath.CRefPath p -> symb_of_path p
    | EcPath.CRefMid  m -> ([], EcIdent.tostring m)

  let string_of_ident = EcIdent.tostring 

  let tv_symb    = fun (_ : t) (x : EcIdent.t  )     -> EcIdent.tostring x
  let ty_symb    = fun (_ : t) (p : EcPath.path)     -> symb_of_path p
  let local_symb = fun (_ : t) (x : EcIdent.t  )     -> EcIdent.tostring x
  let pv_symb    = fun (_ : t) (p : EcPath.epath) _  -> symb_of_epath p
  let fun_symb   = fun (_ : t) (p : EcPath.epath)    -> symb_of_epath p
  let mod_symb   = fun (_ : t) (p : EcPath.cref)     -> symb_of_cref p
  let modty_symb = fun (_ : t) (p : EcPath.path)     -> symb_of_path p
  let op_symb    = fun (_ : t) (p : EcPath.path) _ _ -> symb_of_path p
  let ax_symb    = fun (_ : t) (p : EcPath.path)     -> symb_of_path p
  let th_symb    = fun (_ : t) (p : EcPath.path)     -> symb_of_path p
end
*)
(* -------------------------------------------------------------------- *)
(*module ShortIdentPrinter : IIdentPrinter = struct
  open EcMaps

  type t = { 
    tenv_logic : env;
    tenv_side  : env Mint.t;
    tenv_exc   : Sstr.t;
    tenv_locs  : string EcIdent.Mid.t 
  }

  let init (env, lenv) =
    let exc = 
      List.fold_left 
        (fun exc env ->
          let mv = (preenv env).env_current.amc_variables in
            MMsym.fold (fun s _ exc -> Sstr.add s exc) mv exc)
        Sstr.empty (env::lenv)
    in

    let side =
      List.fold_lefti (fun i s env -> Mint.add i env s) Mint.empty lenv
    in
      { tenv_logic = env;
        tenv_side  = side;
        tenv_exc   = exc;
        tenv_locs  = EcIdent.Mid.empty 
      }

  let add_local t id = 
    let s = EcIdent.name id in
    let s = 
      if not (Sstr.mem s t.tenv_exc) then s 
      else
        let rec aux n = 
          let s = Printf.sprintf "%s%i" s n in
          if Sstr.mem s t.tenv_exc then aux (n+1) else s in
        aux 0 in
    { t with tenv_exc = Sstr.add s t.tenv_exc;
      tenv_locs = EcIdent.Mid.add id s t.tenv_locs 
    }

  let no_locals t = EcIdent.Mid.is_empty t.tenv_locs

  let add fadd t p =
    assert (no_locals t);
    { t with
        tenv_logic = fadd p t.tenv_logic;
        tenv_exc   = Sstr.add (EcPath.basename p) t.tenv_exc;
    }
    
  let add_pvar  = add Var.add
  let add_fun   = add Fun.add
  let add_mod   = add Mod.add
  let add_modty = add ModTy.add
  let add_ty    = add Ty.add
  let add_op    = add Op.add
  let add_ax    = add Ax.add
  let add_th    = add Theory.add

  let shorten_path lookup p env = 
    let rec aux par qs s = 
      try
        let p' = lookup (qs,s) env in
        if not (EcPath.p_equal p p') then raise Not_found; 
        (qs,s)
      with _ -> 
        match par with 
        | [] -> assert false
        | s'::par -> aux par (s'::qs) s in
    let qs, s = EcPath.toqsymbol p in
    aux (List.rev qs) [] s 

  let shorten_epath lookup p env =
    match p with
    | EcPath.EPath p -> shorten_path lookup p env
    | _ -> assert false                 (* FIXME *)

  let shorten_cref lookup p env =
    match p with
    | EcPath.CRefPath p -> shorten_path lookup p env
    | _ -> assert false                 (* FIXME *)

  let tv_symb _t tv = EcIdent.name tv

  let ty_symb t p = 
    shorten_path Ty.lookup_path p t.tenv_logic

  let local_symb t id = EcIdent.Mid.find id t.tenv_locs

  let pv_symb t p o =
    let env = 
      match o with
      | None -> t.tenv_logic 
      | Some i ->
          try Mint.find i t.tenv_side 
          with _ -> t.tenv_logic (* FIXME *)
    in

    let lookup = fun p env ->
      match Var.lookup_path p env with
      | EcPath.CRefPath p -> p
      | _ -> assert false               (* FIXM *)
    in
      shorten_epath lookup p env

  let fun_symb t p =
    let lookup = fun p env ->
      match Fun.lookup_path p env with
      | EcPath.EPath p -> p
      | _ -> assert false               (* FIXME *)
    in
      shorten_epath lookup p t.tenv_logic

  let mod_symb t p = 
    let lookup = fun p env ->
      match Mod.lookup_path p env with
      | EcPath.CRefPath p -> p
      | _ -> assert false               (* FIXME *)
    in
      shorten_cref lookup p t.tenv_logic

  let modty_symb t p = 
    shorten_path ModTy.lookup_path p t.tenv_logic

  let op_symb t p _tvi psig = 
    let lookup = 
      match psig with 
      | None -> Op.lookup_path 
      | Some psig -> 
          fun qs env ->
            let ue = EcUnify.UniEnv.create None in
            match EcUnify.select_op true None env qs ue psig with
            | [ (p,_), _, _ ] -> p
            | _ -> raise Not_found in
    shorten_path lookup p t.tenv_logic 

  let ax_symb t p = 
    shorten_path Ax.lookup_path p t.tenv_logic 

  let th_symb t p = 
    shorten_path Theory.lookup_path p t.tenv_logic 

  let string_of_ident id = EcIdent.name id
end
*)
(*module EcShortPP   = MakePP(ShortIdentPrinter) *)
module EcRawPP     = MakePP(RawIdentPrinter) 
(*module EcLongRawPP = MakePP(LongRawIdentPrinter)  *)
module EcPP        = (*EcShortPP*) EcRawPP

(* -------------------------------------------------------------------- *)
module EcDebugPP = struct
  module BPP = EcRawPP

  let pr_type     = BPP.pr_type ()
  let pr_expr     = BPP.pr_expr ()
  let pr_form     = BPP.pr_form ()
  let pr_dom      = BPP.pr_dom  ()
  let pr_typedecl = fun (x, v) -> BPP.pr_typedecl () (EcPath.psymbol x, v)
  let pr_opdecl   = fun (x, v) -> BPP.pr_opdecl   () (EcPath.psymbol x, v)
  let pr_axiom    = fun (x, v) -> BPP.pr_axiom    () (EcPath.psymbol x, v)
  let pr_modsig   = fun (x, v) -> BPP.pr_modsig   () (EcPath.psymbol x, v)
  let pr_module   = fun     v  -> BPP.pr_module   () (EcPath.psymbol v.me_name, v)
  let pr_export   = BPP.pr_export ()
  let pr_theory   = fun (x, v) -> BPP.pr_theory   () (EcPath.psymbol x, v)
  let pr_lgoal    = BPP.pr_lgoal    ()

  let pp_type     = BPP.pp_type ()
  let pp_expr     = BPP.pp_expr ()
  let pp_form     = BPP.pp_form ()
  let pp_dom      = BPP.pp_dom  ()
  let pp_typedecl = fun fmt (x, v) -> BPP.pp_typedecl () fmt (EcPath.psymbol x, v)
  let pp_opdecl   = fun fmt (x, v) -> BPP.pp_opdecl   () fmt (EcPath.psymbol x, v)
  let pp_axiom    = fun fmt (x, v) -> BPP.pp_axiom    () fmt (EcPath.psymbol x, v)
  let pp_modsig   = fun fmt (x, v) -> BPP.pp_modsig   () fmt (EcPath.psymbol x, v)
  let pp_module   = fun fmt     v  -> BPP.pp_module   () fmt (EcPath.psymbol v.me_name, v)
  let pp_export   = BPP.pp_export ()
  let pp_theory   = fun fmt (x, v) -> BPP.pp_theory   () fmt (EcPath.psymbol x, v)
  let pp_lgoal    = BPP.pp_lgoal    ()

  let rec pp_path fmt p = 
    match p.EcPath.p_node with 
    | EcPath.Pident x      -> Format.fprintf fmt "%s" (EcIdent.name x)
    | EcPath.Psymbol x      -> Format.fprintf fmt "%s" x
    | EcPath.Pqname (p, x) -> Format.fprintf fmt "%a.%s" pp_path p x
end
