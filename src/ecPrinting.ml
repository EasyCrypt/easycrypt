(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcTypes
open EcFol
open EcDecl
open EcModules
open EcTheory
open EcBaseLogic

(* -------------------------------------------------------------------- *)
module Pp : sig
  type doc

  val empty    : doc
  val string   : string -> doc
  val flat     : doc -> doc
  val hardline : doc

  val (!^) : string -> doc

  val (^^)   : doc -> doc -> doc (* concat. without spaces                    *)
  val (^/^)  : doc -> doc -> doc (* concat. with inter-space                  *)
  val (^//^) : doc -> doc -> doc (* concat. with break. inter-space           *)
  val (^@@^) : doc -> doc -> doc (* concat. with break. inter-space + nesting *)

  val fold1 : (doc -> doc -> doc) -> doc list -> doc

  val seq : ?sep:string -> ?break:bool -> ?spacing:(bool * bool) -> doc list -> doc

  val join : doc list -> doc            (* concat. with non-breakable spaces *)
  val glue : doc list -> doc            (* non-breakable concat. (no spaces) *)

  val pretty    : out_channel -> doc -> unit
  val fmtpretty : Format.formatter -> doc -> unit
end = struct
  type blank = int * int option        (* width * nesting/breakable *)

  type doc =
  | DEmpty
  | DHardline
  | DString   of string
  | DCat      of doc * blank * doc
  | DFlat     of doc

  let empty = DEmpty

  let string (s : string) =
    DString s

  let flat (d : doc) =
    DFlat d

  let hardline =
    DHardline

  let (!^) = string

  let (^^) (d1 : doc) (d2 : doc) =
    match d1, d2 with
    | DEmpty, _ -> d2
    | _, DEmpty -> d1
    | _, _ -> DCat (d1, (0, None), d2)

  let (^/^) (d1 : doc) (d2 : doc) =
    DCat (d1, (1, None), d2)

  let (^//^) (d1 : doc) (d2 : doc) =
    DCat (d1, (1, Some 0), d2)

  let (^@@^) (d1 : doc) (d2 : doc) =
    DCat (d1, (1, Some 2), d2)

  let fold1 (f : doc -> doc -> doc) (ds : doc list) =
    match ds with
    | []      -> empty
    | [d]     -> d
    | d :: ds -> List.fold_left f d ds

  let seq ?(sep = "") ?(break = false) ?(spacing = (false, true)) ds =
    fold1 (fun d1 d2 -> d1 ^/^ !^sep ^@@^ d2) ds

  let join = fold1 (^/^)
  let glue = fold1 (^^)

  let compile =
    let rec compile (flat : bool) = function
      | DEmpty    -> Pprint.empty
      | DString s -> Pprint.string s
      | DFlat d   -> compile true d
      | DHardline -> Pprint.ifflat (Pprint.break1) (Pprint.hardline)

      | DCat (d1, (i, b), d2) -> 
        let d1 = compile flat d1
        and d2 =
          let blank =
            if b = None || flat then Pprint.blank else Pprint.break in
          let d2 = compile flat d2 in
          let d2 =
            if i > 0 then Pprint.(^^) (blank i) d2 else d2 in
          let d2 =
            match b with
            | None -> d2
            | Some _ when flat -> d2
            | Some b ->
              let d2 = Pprint.group d2 in
                if b > 0 then Pprint.nest b d2 else d2
          in
            d2
        in
          Pprint.(^^) d1 d2
    in
      compile false

  let pretty stream doc =
    Pprint.Channel.pretty 0.8 80 stream (compile doc)

  let fmtpretty fmt doc =
    Pprint.Formatter.pretty 0.8 80 fmt (compile doc)
end

(* -------------------------------------------------------------------- *)
module EP = EcParser

type ppenv = EcEnv.env

module PPE = struct
  let add_local (ppenv : ppenv) _ =
    ppenv

  let add_pvar  (ppenv : ppenv) pv    = EcEnv.Var.add pv ppenv
  let add_fun   (ppenv : ppenv) f     = EcEnv.Fun.add f ppenv
  let add_mod   (ppenv : ppenv) me    = EcEnv.Mod.add me ppenv
  let add_modty (ppenv : ppenv) modty = EcEnv.ModTy.add modty ppenv
  let add_th    (ppenv : ppenv) th    = EcEnv.Theory.add th ppenv
  let add_ty    (ppenv : ppenv) ty    = EcEnv.Ty.add ty ppenv
  let add_op    (ppenv : ppenv) op    = EcEnv.Op.add op ppenv
  let add_ax    (ppenv : ppenv) ax    = EcEnv.Ax.add ax ppenv

  let shorten (query : qsymbol -> bool) =
    let for1 (nm : symbol list) (x : symbol) =
      if query (nm, x) then Some (nm, x) else None
    in

    let rec doit (nm : symbol list) (x : symbol) =
      match nm with
      | [] -> for1 [] x
      | r :: subnm -> begin
          match doit subnm x with
          | Some qs -> Some qs
          | None    -> for1 nm x
      end
    in

      fun (p : EcPath.path) ->
        let (nm, x) = EcPath.toqsymbol p in
          match doit nm x with
          | Some qs -> qs
          | None -> (nm, x)

  let th_symb (ppenv : ppenv) (p : EcPath.path) =
    let query qs = EcEnv.Theory.lookup_opt qs ppenv <> None in
      shorten query p

  let tyname_symb (ppenv : ppenv) (p : EcPath.path) =
    let query qs = EcEnv.Theory.lookup_opt qs ppenv <> None in
      shorten query p

  let op_symb (ppenv : ppenv) (p : EcPath.path) =
    let query qs = EcEnv.Op.lookup_opt qs ppenv <> None in
      shorten query p    
end

(* -------------------------------------------------------------------- *)
let (!^)   = Pp.(!^)
let (^^)   = Pp.(^^)
let (^/^)  = Pp.(^/^)
let (^//^) = Pp.(^//^)
let (^@@^) = Pp.(^@@^)

(* -------------------------------------------------------------------- *)
let tk_as     = !^"as"
let tk_assert = !^"assert"
let tk_axiom  = !^"axiom"
let tk_clone  = !^"clone"
let tk_cnst   = !^"cnst"
let tk_else   = !^"else"
let tk_end    = !^"end"
let tk_exists = !^"exists"
let tk_export = !^"export"
let tk_flip   = !^"{0,1}"
let tk_forall = !^"forall"
let tk_fun    = !^"fun"
let tk_if     = !^"if"
let tk_in     = !^"in"
let tk_lambda = !^"lambda"
let tk_lemma  = !^"lemma"
let tk_let    = !^"let"
let tk_memory = !^"memory"
let tk_module = !^"module"
let tk_op     = !^"op"
let tk_pred   = !^"pred"
let tk_then   = !^"then"
let tk_theory = !^"theory"
let tk_type   = !^"type"
let tk_var    = !^"var"
let tk_while  = !^"while"
let tk_with   = !^"with"

let tk_from_int = !^"%r"
let tk_tild     = !^"~"
let tk_arrow    = !^"->"
let tk_larrow   = !^"<-"
let tk_pipe     = !^"|"
let tk_dotdot   = !^".."

(* -------------------------------------------------------------------- *)
let pr_paren   d = Pp.glue [!^"("; d; !^")"]
let pr_bracket d = Pp.glue [!^"["; d; !^"]"]
let pr_brace   d = Pp.glue [!^"{"; d; !^"}"]
let pr_angle   d = Pp.glue [!^"<"; d; !^">"]

let pr_dotted d = d ^^ !^"."

let pr_block (docs : Pp.doc list) =
  Pp.fold1
    (fun d1 d2 -> d1 ^^ Pp.hardline ^^ d2)
    docs

let pr_mblocks (docs : (Pp.doc list) list) =
  let hardline2 = Pp.hardline ^^ Pp.hardline in

  let docs =
    List.map
      (Pp.fold1 (fun d1 d2 -> d1 ^^ Pp.hardline ^^ d2))
      docs
  in
    Pp.fold1
      (fun d1 d2 -> d1 ^^ hardline2 ^^ d2)
      docs

(* -------------------------------------------------------------------- *)
let is_ident_symbol name = 
  match EcIo.lex_single_token name with
  | Some EP.LIDENT _ -> true
  | Some EP.UIDENT _ -> true
  | _ -> false

let pr_qsymbol ((nm, x) : qsymbol) =
  let pr_symbol (x : symbol) =
    if is_ident_symbol x then x else Printf.sprintf "[%s]" x
  in

  let x  = pr_symbol x
  and nm = List.map pr_symbol nm in
    match nm with
    | [] -> !^ x
    | _  -> !^ (Printf.sprintf "%s.%s" (String.concat "." nm) x)

(* -------------------------------------------------------------------- *)
let pr_univar (_ppe : ppenv) (i : _) =
  !^ (Printf.sprintf "#%d" i)

let pr_tvar (_ppe : ppenv) (a : EcIdent.t) =
  !^ (EcIdent.tostring a)

let pr_tyname (ppe : ppenv) (p : EcPath.path) =
  pr_qsymbol (PPE.tyname_symb ppe p)

let pr_ident (_ppe : ppenv) (x : EcIdent.t) =
  !^ (EcIdent.tostring x)

let pr_local (_ppe : ppenv) (x : EcIdent.t) =
  !^ (EcIdent.tostring x)

let pr_funname (_ppe : ppenv) (p : EcPath.mpath) =
  !^ (EcPath.m_tostring p)

let pr_thname (_ppe : ppenv) (p : EcPath.path) =
  !^ (EcPath.tostring p)

let pr_pv (_ppe : ppenv) (x : prog_var) =
  !^ (EcPath.m_tostring x.pv_name)

(* -------------------------------------------------------------------- *)
let pr_type (ppe : ppenv) (ty : ty) =
  let rec pr_type btuple (ty : ty) =
    match ty.ty_node with
    | Tunivar ui -> pr_univar ppe ui
    | Tvar    a  -> pr_tvar ppe a

    | Ttuple tys ->
        let doc = List.map (pr_type true) tys in
        let doc = Pp.seq ~sep:"*" ~spacing:(true, true) doc in
          if btuple then pr_paren doc else doc

    | Tconstr (name, tyargs) -> begin
        let name = pr_tyname ppe name in
          match tyargs with
          | []   -> name
          | [ty] -> (pr_type true ty) ^/^ name
          | _    -> (Pp.join (List.map (pr_type false) tyargs)) ^/^ name
      end

    | Tfun (ty1, ty2) ->
        let d1 = pr_type true  ty1
        and d2 = pr_type false ty2 in
          d1 ^/^ tk_arrow ^@@^ d2
  in
    pr_type false ty

(* -------------------------------------------------------------------- *)
type assoc  = [`Left | `Right | `NonAssoc]
type fixity = [`Prefix | `Postfix | `Infix of assoc]
type opprec = int * fixity

(* -------------------------------------------------------------------- *)
let maybe_paren (outer, side) inner doc =
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
    | false -> pr_paren doc

(* -------------------------------------------------------------------- *)
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

(* -------------------------------------------------------------------- *)
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

(* -------------------------------------------------------------------- *)
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

(* -------------------------------------------------------------------- *)
let is_binop name =
  (priority_of_binop_name name) <> None

(* -------------------------------------------------------------------- *)
let pr_if3 (ppenv : ppenv) pr_sub outer b e1 e2 =
  let dc  = pr_sub ppenv (e_bin_prio_if3, `Left    ) b  in
  let d1  = pr_sub ppenv (min_op_prec   , `NonAssoc) e1 in
  let d2  = pr_sub ppenv (e_bin_prio_if3, `Right   ) e2 in
  let doc = Pp.join [dc; !^"?"; d1; !^":"; d2] in
    maybe_paren outer e_bin_prio_if3 doc

(* -------------------------------------------------------------------- *)
let pr_if (ppenv : ppenv) pr_sub outer b e1 e2 =
  let dc  = pr_sub ppenv (min_op_prec  , `NonAssoc) b  in
  let d1  = pr_sub ppenv (min_op_prec  , `NonAssoc) e1 in
  let d2  = pr_sub ppenv (e_bin_prio_if, `Right   ) e2 in
  let doc = Pp.join [tk_if; dc; tk_then; d1; tk_else; d2] in
    maybe_paren outer e_bin_prio_if doc

(* -------------------------------------------------------------------- *)
let pr_let (ppenv : ppenv) pr_sub outer pt e1 e2 =
  let ids = lp_ids pt in
  let subppenv = List.fold_left PPE.add_local ppenv ids in

  let dpt = Pp.seq ~sep:"," (List.map (pr_local subppenv) ids) in

  let d1  = pr_sub ppenv (e_bin_prio_letin, `NonAssoc) e1 in
  let d2  = pr_sub subppenv (e_bin_prio_letin, `NonAssoc) e2 in
  let doc = Pp.join [tk_let; dpt; !^"="; d1; tk_in; d2] in
    maybe_paren outer e_bin_prio_letin doc

(* -------------------------------------------------------------------- *)
let pr_tuple_expr (ppenv : ppenv) pr_sub es =
  let docs = List.map (pr_sub ppenv (min_op_prec, `NonAssoc)) es in
    pr_paren (Pp.seq ~sep:"," docs)

(* -------------------------------------------------------------------- *)
let pr_op_name (ppenv : ppenv) (p : EcPath.path) =
  pr_qsymbol (PPE.op_symb ppenv p)

(* -------------------------------------------------------------------- *)
let pr_opapp (ppenv : ppenv) pr_sub outer op tvi es =
  let (nm, opname) = PPE.op_symb ppenv op in
  
  let pr_as_std_op () =
    let (doc, prio) =
      if nm = [] then
        match opname, es with
        | "__nil", [] ->
            (pr_bracket Pp.empty, max_op_prec)

        | "__abs", [e] -> 
            let e = pr_sub ppenv (min_op_prec, `NonAssoc) e in
              (Pp.glue [tk_pipe; e; tk_pipe], appprio)

        | "__get", [e1; e2] ->
            let e1 = pr_sub ppenv (e_get_prio , `Left)     e1 in
            let e2 = pr_sub ppenv (min_op_prec, `NonAssoc) e2 in

            let doc = Pp.join [e1; pr_bracket e2] in
              (doc, e_get_prio)

        | "__set", [e1; e2; e3] ->
            let e1 = pr_sub ppenv (e_get_prio , `Left    ) e1 in
            let e2 = pr_sub ppenv (min_op_prec, `NonAssoc) e2 in
            let e3 = pr_sub ppenv (min_op_prec, `NonAssoc) e3 in

            let doc = Pp.join [e1; pr_bracket (Pp.join [e2; tk_larrow; e3])] in
              (doc, e_get_prio)

        | _ ->
            let es = List.map (pr_sub ppenv (appprio, `Right)) es in
              (Pp.join ((pr_qsymbol (nm, opname)) :: es), appprio)
      else 
        let es = List.map (pr_sub ppenv (appprio, `Right)) es in
          (Pp.join ((pr_qsymbol (nm, opname)) :: es), appprio)
    in
      maybe_paren outer prio doc

  and try_pr_as_uniop () =
    if nm = [] then
      match es with
      | [e] ->
          begin match priority_of_uniop opname with
          | None -> None
          | Some opprio  ->
              let opprio = (opprio, `Prefix) in
              let doc =
                !^ opname ^^ (pr_sub ppenv (opprio, `NonAssoc) e)
              in
              Some (maybe_paren outer opprio doc)
          end
      | _ -> None
    else None

  and try_pr_as_binop () =
    if nm = [] then
      match es with
      | [e1; e2] ->
          begin match priority_of_binop_name opname with
          | None -> None
          | Some opprio ->
              let d1  = pr_sub ppenv (opprio, `Left ) e1 in
              let d2  = pr_sub ppenv (opprio, `Right) e2 in
              let doc = Pp.join [d1; !^ opname ; d2] in
              Some (maybe_paren outer opprio doc)
          end
      | _ -> None
    else None
        
  and try_pr_special () = 
    let qs = EcPath.toqsymbol op in
    match es with
    | [] when qs = EcCoreLib.s_dbool ->
        Some tk_flip

    | [e] when qs = EcCoreLib.s_dbitstring ->
        let e = pr_sub ppenv (max_op_prec, `NonAssoc) e in
          Some (Pp.glue [tk_flip; tk_tild; e])

    | [e] when qs = EcCoreLib.s_from_int ->
        let e = pr_sub ppenv (max_op_prec, `NonAssoc) e in
          Some (Pp.glue [e; tk_from_int])

    | [e1; e2] when qs = EcCoreLib.s_dinter ->
        let e1 = pr_sub ppenv (min_op_prec, `NonAssoc) e1 in
        let e2 = pr_sub ppenv (min_op_prec, `NonAssoc) e2 in
          Some (pr_bracket (Pp.glue [e1; tk_dotdot; e2]))

    | _ -> None

  in
    ofdfl pr_as_std_op
      (List.fpick [try_pr_special ;
                   try_pr_as_uniop;
                   try_pr_as_binop])

(* -------------------------------------------------------------------- *)
let pr_expr (ppenv : ppenv) (e : expr) =
  let rec pr_expr (ppenv : ppenv) outer (e : expr) =
    match e.e_node with
    | Evar x ->
        pr_pv ppenv x

    | Elocal x ->
        pr_local ppenv x

    | Eop (op, tys) -> (* FIXME infix, prefix, ty_inst *)
        pr_op_name ppenv op

    | Eint i ->
        !^ (string_of_int i)

    | Eif (c, e1, e2) ->
        pr_if ppenv pr_expr outer c e1 e2

    | Etuple es ->
        pr_tuple_expr ppenv pr_expr es

    | Eapp ({e_node = Eop (op, tys) }, args) ->
        pr_opapp ppenv pr_expr outer op tys args

    | Eapp (e, args) -> 
        let e    = pr_expr ppenv (max_op_prec, `NonAssoc) e in
        let args = List.map (pr_expr ppenv (min_op_prec, `NonAssoc)) args in
          e ^^ (pr_paren (Pp.seq ~sep:"," args))

    | Elet (pt, e1, e2) ->
        pr_let ppenv pr_expr outer pt e1 e2

  in
    pr_expr ppenv (min_op_prec, `NonAssoc) e

(* MODULE PPRINTING *)

(* -------------------------------------------------------------------- *)
let pr_lvalue (ppenv : ppenv) (lv : lvalue) =
  match lv with
  | LvVar (p, _) ->
      pr_pv ppenv p

  | LvTuple ps ->
      let ps = List.map ((pr_pv ppenv) -| fst) ps in
        pr_paren (Pp.seq ~sep:"," ps)

  | LvMap (_, x, e, _) ->
      (pr_pv ppenv x) ^^ (pr_bracket (pr_expr ppenv e))

(* -------------------------------------------------------------------- *)
let rec pr_instr (ppenv : ppenv) (i : instr) =
  let doc =
    match i.i_node with
    | Sasgn (lv, e) ->
        Pp.join [pr_lvalue ppenv lv; !^"="; pr_expr ppenv e]

    | Srnd (lv, e) ->
        Pp.join [pr_lvalue ppenv lv; !^"="; !^"$"; pr_expr ppenv e]

    | Scall (lv, name, args) -> begin
        let doc = 
          let name = pr_funname ppenv name in
          let args = List.map (pr_expr ppenv) args in
            name ^^ (pr_paren (Pp.seq ~sep:"," args))
        in
          match lv with
          | None    -> doc
          | Some lv -> Pp.join [pr_lvalue ppenv lv; !^"="; doc]
      end

    | Sassert e ->
        Pp.join [tk_assert; pr_paren (pr_expr ppenv e)]

    | Sif (e, b1, b2) ->
        let e  = pr_paren (pr_expr ppenv e) in
        let b1 = pr_bracket (pr_stmt ppenv b1) in
        let b2 = pr_bracket (pr_stmt ppenv b2) in
          Pp.join [tk_if; e; b1; tk_else; b2]

    | Swhile (e, body) ->
        let e = pr_paren (pr_expr ppenv e) in
        let body = pr_bracket (pr_stmt ppenv body) in
          Pp.join [tk_while; e; body]

  in
    doc ^^ !^";"

(* -------------------------------------------------------------------- *)
and pr_stmt (ppenv : ppenv) (s : stmt) =
  Pp.join (List.map (pr_instr ppenv) s.s_node)

(* -------------------------------------------------------------------- *)
let rec pr_module_item (scope : EcPath.path) (ppenv : ppenv) (item : module_item) =
  let xpath x = EcPath.pqname scope x in

    match item with
    | MI_Variable v ->
        let doc = pr_modvar ppenv (xpath v.v_name, v) in
          (PPE.add_pvar ppenv (xpath v.v_name), doc)

    | MI_Function f ->
        let doc = pr_modfun ppenv (xpath f.f_name, f) in
          (PPE.add_fun ppenv (xpath f.f_name), doc)

    | MI_Module me ->
        let doc = pr_module ppenv (xpath me.me_name, me) in
          (PPE.add_mod ppenv (xpath me.me_name), doc)

(* -------------------------------------------------------------------- *)
and pr_modvar (ppenv : ppenv) ((_, v) : EcPath.path * variable) =
  Pp.join [tk_var; !^(v.v_name); !^":"; pr_type ppenv v.v_type]

(* -------------------------------------------------------------------- *)
and pr_modfun (ppenv : ppenv) ((_, f) : EcPath.path * function_) =
  let fname = f.f_sig.fs_name in
  let fparams, fres = f.f_sig.fs_sig in

  let dparams =
    List.map
      (fun vd -> Pp.join [!^(vd.v_name); !^":"; pr_type ppenv vd.v_type])
      fparams in
  let dparams = pr_paren (Pp.seq ~sep:"," dparams) in

  let prelude =
    Pp.join [tk_fun; !^fname ^^ dparams; !^":"; pr_type ppenv fres]
  in

    match f.f_def with
    | None ->
        prelude

    | Some def ->
        let dlocals =
          List.map
            (fun vd -> pr_local ppenv (EcIdent.create vd.v_name))
            def.f_locals

        and dbody =
          let bodyppenv =
            List.fold_left
              (fun ppenv x -> PPE.add_local ppenv (EcIdent.create x.v_name))
              ppenv
              ((fst f.f_sig.fs_sig) @ def.f_locals)
          in
            List.map (pr_instr bodyppenv) def.f_body.s_node
        in
          (Pp.join [prelude; !^"="]) ^/^ (pr_mblocks [dlocals; dbody])

(* -------------------------------------------------------------------- *)
and pr_module (ppenv : ppenv) ((p, m) : EcPath.path * module_expr) =
  let mename  = m.me_name in
  let prelude = Pp.join [tk_module; !^mename] in
  let moddoc  =

    match m.me_body with
    | ME_Alias m -> 
        Pp.join [prelude; !^"="; !^ (EcPath.m_tostring m)]

    | ME_Decl _modty ->
        assert false                  (* FIXME *)

    | ME_Structure mstruct ->
        let _, bodydoc =
          List.map_fold (pr_module_item p) ppenv mstruct.ms_body
        in
              (Pp.join [prelude; !^"="])
          ^/^ (pr_brace (pr_block bodydoc))
  in
    pr_dotted moddoc

(* -------------------------------------------------------------------- *)
let pr_modtype (_ppenv : ppenv) (_ : module_type) =
  Pp.empty                            (* FIXME *)

(* -------------------------------------------------------------------- *)
let pr_typedecl (ppenv : ppenv) ((x, tyd) : EcPath.path * tydecl) =
  let basename = EcPath.basename x in
  let dparams =
    match tyd.tyd_params with
    | []  -> Pp.empty
    | [a] -> pr_tvar ppenv a
    | la  -> pr_paren (Pp.seq ~sep:"," (List.map (pr_tvar ppenv) la))
  in

  let doc = tk_type ^//^ dparams ^^ (!^basename) in
  let doc =
    match tyd.tyd_type with
    | None    -> doc
    | Some ty -> doc ^//^ !^"=" ^//^ (pr_type ppenv ty)
  in
    pr_dotted doc

(* -------------------------------------------------------------------- *)
let pr_binding (ppenv : ppenv) (x, ty) =
  match ty with
  | GTty ty ->
      let tenv1 = PPE.add_local ppenv x in
        (tenv1, Pp.join [pr_local tenv1 x; !^":"; pr_type ppenv ty])

  | GTmem _ ->                          (* FIXME *)
      let ppenv1 = PPE.add_local ppenv x in
        (ppenv1, Pp.join [pr_local ppenv1 x; !^":"; tk_memory])

  | GTmodty p ->
      let ppenv1 = PPE.add_local ppenv x in
        (ppenv1, Pp.join [pr_local ppenv1 x; !^":"; pr_modtype ppenv p])

(* -------------------------------------------------------------------- *)
let pr_bindings (ppenv : ppenv) (b : binding) =
  let ppenv, bs = List.map_fold pr_binding ppenv b in
    ppenv, pr_paren (Pp.seq ~sep:"," bs)

(* -------------------------------------------------------------------- *)
let tk_quant = function
  | Lforall -> tk_forall
  | Lexists -> tk_exists
  | Llambda -> tk_lambda

(* -------------------------------------------------------------------- *)
let pr_form (ppenv : ppenv) (f : form) =
  let rec pr_form (ppenv : ppenv) outer (f : form) =
    match f.f_node with
    | Fint n ->
        !^ (string_of_int n)

    | Flocal id ->
        pr_local ppenv id

    | Fpvar (x, i) ->                 (* FIXME *)
        Pp.join [pr_pv ppenv x; pr_brace (pr_local ppenv i)]

    | Fquant (q, bd, f) ->
        let (subppenv, dd) = pr_bindings ppenv bd in 
          Pp.join [tk_quant q; dd^^(!^","); pr_form subppenv outer f]

    | Fif (b, f1, f2) ->
        pr_if ppenv pr_form outer b f1 f2

    | Flet (lp, f1, f2) ->
        pr_let ppenv pr_form outer lp f1 f2

    | Fop(op, tvi) ->		    (* FIXME infix, prefix, ty_inst *)
        pr_op_name ppenv op

    | Fapp ({f_node = Fop (p, tys)}, args) ->
        pr_opapp ppenv pr_form outer p tys args

    | Fapp (e, args) ->
        let e    = pr_form ppenv (max_op_prec, `NoneAssoc) e in
        let args = List.map (pr_form ppenv (min_op_prec, `NonAssoc)) args in

          e ^^ (pr_paren (Pp.seq ~sep:"," args))

    | Ftuple args ->
        pr_tuple_expr ppenv pr_form args

    | FhoareF _ ->
        !^ "implement-me"             (* FIXME *)
          
    | FhoareS hs -> 
        let dbody =
          let bodyppenv = ppenv in
            List.map (pr_instr bodyppenv) hs.hs_s.s_node
        in
          Pp.join [
            pr_brace (pr_form ppenv outer hs.hs_pr);
            pr_mblocks [dbody];
            pr_brace (pr_form ppenv outer hs.hs_po);
          ]

    | FequivF _ | FequivS _ | Fpr _ | FeqGlob _ ->
        !^ "implement-me"  (* FIXME *)
  in
    pr_form ppenv (min_op_prec, `NonAssoc) f

(* -------------------------------------------------------------------- *)
let pr_fct_def ppenv def = 
  let dlocals =
    List.map
      (fun x -> pr_local ppenv (EcIdent.create x.v_name))
      def.f_locals
  and dbody =
    let bodyppenv =
      List.fold_left
        (fun ppenv x -> PPE.add_local ppenv (EcIdent.create x.v_name))
        ppenv
        def.f_locals
    in
    List.map (pr_instr bodyppenv) def.f_body.s_node
  in
  pr_mblocks [dlocals; dbody]

(* -------------------------------------------------------------------- *)
let pr_tyvarsdecl (ppenv : ppenv) ids =
  if ids = [] then
    Pp.empty
  else
    pr_bracket (Pp.join (List.map (pr_tvar ppenv) ids))

let pr_vardecl (ppenv : ppenv) (x, ty) =
  let tenv1 = PPE.add_local ppenv x in
    (tenv1, Pp.join [pr_local tenv1 x; !^":"; pr_type ppenv ty])

let pr_vardecls (ppenv : ppenv) ds =
  let ppenv, ds = List.map_fold pr_vardecl ppenv ds in
    (ppenv, pr_paren (Pp.seq ~sep:"," ds))

let pr_dom (ppenv : ppenv) dom =
  pr_paren (Pp.seq ~sep:"*"(List.map (pr_type ppenv) dom))

let pr_sig (ppenv : ppenv) (dom, codom) =
  match dom with
  | [] -> pr_type ppenv codom
  | _  -> (pr_dom ppenv dom) ^//^ tk_arrow ^//^ (pr_type ppenv codom)

let pr_opdecl (ppenv : ppenv) ((x, op) : EcPath.path * operator) =
  let basename = EcPath.basename x in

  let dop, ddecl =
    match op.op_kind with
    | OB_oper i ->
        let dop = if op.op_dom = [] then tk_cnst else tk_op in
        let ddecl =
          match i with
          | None -> Pp.join [!^":"; pr_sig ppenv (op_sig op)]
          | Some (ids, e) ->
              let vardecls = List.combine ids op.op_dom in
              let subppenv, dd = pr_vardecls ppenv vardecls in
                Pp.join [
                  dd; !^":"; pr_type ppenv op.op_codom;
                  !^"="; pr_expr subppenv e]
        in
          (dop, ddecl)

    | OB_pred i ->
        let ddecl =
          match i with
          | None -> Pp.join [!^":"; pr_dom ppenv op.op_dom]
          | Some (ids, f) ->
              let vardecls = List.combine ids op.op_dom in
              let subppenv, dd = pr_vardecls ppenv vardecls in
                Pp.join [dd; !^"="; pr_form subppenv f]
        in
        tk_pred, ddecl in

  let doc =
    Pp.join [dop; !^basename; pr_tyvarsdecl ppenv op.op_params; ddecl]
  in
    pr_dotted doc

(* -------------------------------------------------------------------- *)
let pr_axiom (ppenv : ppenv) ((x, ax) : EcPath.path * axiom) =
  let basename = EcPath.basename x in

  let tk =
    match ax.ax_kind with
    | Axiom   -> tk_axiom
    | Lemma _ -> tk_lemma

  and pr_name =
    match ax.ax_params with
    | [] -> !^basename
    | _  -> 
        let args = List.map (pr_ident ppenv) ax.ax_params in
          !^basename ^^ (pr_angle (Pp.seq ~sep:"," args))

  and spec =
    match ax.ax_spec with
    | None   -> !^"<why3-imported>"
    | Some f -> pr_form ppenv f
  in

    pr_dotted (Pp.join [tk; pr_name; !^":"; spec])

(* -------------------------------------------------------------------- *)
let pr_modsig (_ppenv : ppenv) ((x, _tymod) : EcPath.path * module_sig) =
  let basename = EcPath.basename x in
    pr_dotted (Pp.join [tk_module; tk_type; !^basename; !^"="])

(* -------------------------------------------------------------------- *)
let pr_export (ppenv : ppenv) (p : EcPath.path) =
  pr_dotted (tk_export ^//^ (pr_thname ppenv p))

(* -------------------------------------------------------------------- *)
let rec pr_ctheory_item (scope : EcPath.path) (ppenv : ppenv) (item : ctheory_item) =
  let xpath x = EcPath.pqname scope x in

  match item with
  | CTh_type (x, ty) ->
      let doc = pr_typedecl ppenv (xpath x, ty) in
        (PPE.add_ty ppenv (xpath x), doc)

  | CTh_operator (x, op) ->
      let doc = pr_opdecl ppenv (xpath x, op) in
        (PPE.add_op ppenv (xpath x), doc)

  | CTh_axiom (x, ax) ->
      let doc = pr_axiom ppenv (xpath x, ax) in
        (PPE.add_ax ppenv (xpath x), doc)

  | CTh_modtype (x, ty) ->
      let doc = pr_modsig ppenv (xpath x, ty) in
        (PPE.add_modty ppenv (xpath x), doc)

  | CTh_module m ->
      let doc = pr_module ppenv (xpath m.me_name, m) in
        (PPE.add_mod ppenv (xpath m.me_name), doc)

  | CTh_theory (x, th) ->
      let doc = pr_theory ppenv (xpath x, th) in
        (PPE.add_th ppenv (xpath x), doc)

  | CTh_export p ->
      (ppenv, pr_export ppenv p)

(* -------------------------------------------------------------------- *)
and pr_theory (ppenv : ppenv) ((name, ctheory) : EcPath.path * ctheory) =
  let pr_ext ((x, e) : EcIdent.t * ctheory_override) =
    match e with
    | CTHO_Type ty ->
        Pp.join [tk_type; pr_ident ppenv x; !^"="; pr_type ppenv ty]
  in
    match ctheory.cth_desc with
    | CTh_clone p ->
        let doc = [tk_clone; pr_thname ppenv p.cthc_base] in
        let doc =
          let name1 = EcPath.basename name
          and name2 = EcPath.basename p.cthc_base in
            match name1 = name2 with
            | true  -> doc
            | false -> doc @ [tk_as; !^(EcPath.basename name)] in
        let doc =
          match p.cthc_ext with
          | [] -> doc
          | _  ->
            let pext = List.map pr_ext p.cthc_ext in
            let pext = [tk_with; (Pp.seq ~sep:"," pext)] in
              doc @ pext
        in
          Pp.join doc

    | CTh_struct cstruct ->
        let basename = EcPath.basename name in
        let _, pr_cstruct =
          List.map_fold (pr_ctheory_item name) ppenv cstruct
        in
          pr_mblocks
            [[pr_dotted (tk_theory ^//^ !^basename)];
             pr_cstruct;
             [pr_dotted (tk_end    ^//^ !^basename)]]

(* -------------------------------------------------------------------- *)
let pp_path (fmt : Format.formatter) (p : EcPath.path) =
  Format.printf "%s" (EcPath.tostring p)

let pp_type (ppenv : ppenv) (fmt : Format.formatter) ty =
  Pp.fmtpretty fmt (pr_type ppenv ty)

let pp_dom (ppenv : ppenv) (fmt : Format.formatter) dom =
  Pp.fmtpretty fmt (pr_dom ppenv dom)

let pp_form (ppenv : ppenv) (fmt : Format.formatter) (f : form) =
  Pp.fmtpretty fmt (pr_form ppenv f)
