(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols
open EcTypes
open EcFol
open EcDecl
open EcModules
open EcTheory
open EcBaseLogic

(* -------------------------------------------------------------------- *)

module Pp = Pprint
let (!^) = Pp.string
let (^^) = Pp.(^^)
let (^/^) d1 d2 = d1 ^^ !^" " ^^ d2
let (^//^) x y = x ^^ Pp.break1 ^^ y
let (^@@^) x ?(nest=2) y = 
  Pp.group (x ^^ Pp.nest nest (Pp.break1 ^^ y))
let glue  = Pp.fold1 (^^)
let join  = Pp.fold1 (^/^)

let seq ?(sep=",") ?(nest=2) docs =
  Pp.fold1 (fun d1 d2 -> (^@@^) (d1 ^^ !^sep) ~nest d2) docs

let seqc0  = seq ~sep:"," ~nest:0 

(* -------------------------------------------------------------------- *)
module EP = EcParser

type ppenv = 
  { pp_env : EcEnv.env;
    pp_loc : string EcIdent.Mid.t;
    pp_s   : Sstr.t
  }

let empty env = 
  { pp_env = env;
    pp_loc = EcIdent.Mid.empty;
    pp_s   = Sstr.empty }

module PPE = struct
    
  let add_local (ppenv : ppenv) x =
    let s = 
      let s = EcIdent.name x in
      if Sstr.mem s ppenv.pp_s then
        let rec aux n =
          let s = Format.sprintf "%s%i" s n in
          if Sstr.mem s ppenv.pp_s then aux (n+1) 
          else s in
        aux 0 
      else s in
    { ppenv with
      pp_loc = EcIdent.Mid.add x s ppenv.pp_loc;
      pp_s   = Sstr.add s ppenv.pp_s
    }

  let add_pvar  (ppenv : ppenv) pv    = 
    { ppenv with pp_env = EcEnv.Var.add pv ppenv.pp_env }
  let add_fun   (ppenv : ppenv) f     = 
    { ppenv with pp_env = EcEnv.Fun.add f ppenv.pp_env }
  let add_mod   (ppenv : ppenv) me    = 
    { ppenv with pp_env = EcEnv.Mod.add me ppenv.pp_env }
  let add_modty (ppenv : ppenv) modty = 
    { ppenv with pp_env = EcEnv.ModTy.add modty ppenv.pp_env }
  let add_th    (ppenv : ppenv) th    = 
    { ppenv with pp_env = EcEnv.Theory.add th ppenv.pp_env }
  let add_ty    (ppenv : ppenv) ty    = 
    { ppenv with pp_env = EcEnv.Ty.add ty ppenv.pp_env }
  let add_op    (ppenv : ppenv) op    = 
    { ppenv with pp_env = EcEnv.Op.add op ppenv.pp_env }
  let add_ax    (ppenv : ppenv) ax    = 
    { ppenv with pp_env = EcEnv.Ax.add ax ppenv.pp_env }
      
  let check_empty ppenv (nm,s) =
    nm <> [] || not (Sstr.mem s ppenv.pp_s)
 
  let shorten (lookup : qsymbol -> EcEnv.env -> EcPath.path) 
              (ppenv  : ppenv) (p:EcPath.path) =
    let for1 (nm : symbol list) (x : symbol) =
      let qs = (nm,x) in
      try 
        if EcPath.p_equal (lookup qs ppenv.pp_env) p && 
          check_empty ppenv qs then Some qs 
        else None
      with _ -> None
    in

    let rec doit (nm : symbol list) (x : symbol) =
      match nm with
      | [] -> for1 [] x
      | _ :: subnm -> begin
        match doit subnm x with
        | Some qs -> Some qs
        | None    -> for1 nm x
      end
    in
    let (nm, x) = EcPath.toqsymbol p in
    match doit nm x with
    | Some qs -> qs
    | None -> (nm, x)

  let loc_symb ppenv x = 
    try EcIdent.Mid.find x ppenv.pp_loc 
    with _ -> EcIdent.name x 

  let ty_symb = shorten EcEnv.Ty.lookup_path 

  let op_symb = shorten EcEnv.Op.lookup_path

  let ax_symb = shorten EcEnv.Ax.lookup_path

  let th_symb = shorten EcEnv.Theory.lookup_path
    
  let mty_symb = shorten EcEnv.ModTy.lookup_path 

  let rec shorten_m (_ppenv  : ppenv) (p:EcPath.mpath) =
    EcPath.m_tostring p
(*
    let for1 (nm : symbol list) (x : symbol)  =
      let qs = (nm,x) in
      try 
        let (mp, _) = EcEnv.Mod.sp_lookup qs ppenv.pp_env in
        if EcPath.mt_equal mp p.EcPath.m_top then Some qs 
        else None
      with _ -> None
    in

    let rec doit (nm : symbol list) (x : symbol) =
      match nm with
      | [] -> for1 [] x
      | _ :: subnm -> begin
        match doit subnm x with
        | Some qs -> Some qs
        | None    -> for1 nm x
      end
    in
    let (nm, x) = EcPath.toqsymbol p.EcPath.m_path in
    let (nm, x) = match doit nm x with Some qs -> qs | None -> (nm, x) in
    let r = List.take (List.length nm + 1) p.EcPath.m_args in
    let r = List.map (List.map (shorten_m ppenv)) r in
    let a = List.hd r and r = List.rev (List.tl r) in
    List.combine nm r @ [x,a]
*)
  let rec shorten_mx _ppenv xp =
    EcPath.x_tostring xp
    (*
    match EcPath.m_split p with
    | Some(p,EcPath.PKother,s,a) ->
      assert (a = []);
      shorten_mx ppenv p @ [s,[]]
    | Some(_,EcPath.PKmodule,_,_) ->
      shorten_m ppenv p
    | _ -> assert false *)
      
  let mod_symb = shorten_m 
  let fun_symb = shorten_mx
  let pv_symb ppenv pv = shorten_mx ppenv pv.pv_name
    

(*  let shorten_m (ppenv : ppenv) (p:EcPath.mpath) =
    let 
*)   

(*  let fun_symb (ppenv : ppenv) (p : EcPath.path) =
    let query qs = EcEnv.Fun.lookup_opt qs ppenv <> None in
      shorten query p *)
         
        

end

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
let tk_return = !^"return"
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
let tk_dot      = !^"."
let tk_dotdot   = !^".."
let tk_eq       = !^"="

(* -------------------------------------------------------------------- *)
let pr_paren   = Pp.parens
let pr_bracket = Pp.brackets
let pr_brace   = Pp.braces
let pr_angle   = Pp.angles

let pr_dotted d = d ^^ !^"."

let pr_column docs =
  Pp.fold1 (^//^) docs

let pr_column2 docs = 
  Pp.break0 ^^
    Pp.fold1 (fun x y -> x ^^ Pp.break0 ^^ Pp.break0 ^^ y) docs ^^
    Pp.break0

let pr_br_block doc =
  if doc = Pp.empty then pr_brace Pp.empty 
  else
    pr_brace ((Pp.nest 2 (Pp.break0 ^^ doc)) ^^ Pp.break0)

let pr_block docs = 
  Pp.fold1
    (fun d1 d2 -> d1 ^^ Pp.break1 ^^ d2)
    docs

let pr_mblocks docs = 
  let hardline2 = Pp.break1 ^^ Pp.break1 in

  let docs =
    List.map
      (Pp.fold1 (fun d1 d2 -> d1 ^^ Pp.break1 ^^ d2))
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

let rec pr_msymbol qm = 
  match qm with
  | [] -> assert false
  | [x,args] -> !^x ^^ pr_margs args
  | (x,args) :: qm -> !^x ^^ pr_margs args ^^ tk_dot ^^ pr_msymbol qm
and pr_margs args = 
  if args = [] then Pp.empty
  else pr_paren (seqc0 (List.map pr_msymbol args))
  

let pr_qsymbol ((nm, x) : qsymbol) =
  let pr_symbol (x : symbol) =
    if is_ident_symbol x then x else Printf.sprintf "(%s)" x
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
  !^ (EcIdent.name a)

let pr_tyname (ppe : ppenv) (p : EcPath.path) =
  pr_qsymbol (PPE.ty_symb ppe p)

let pr_ident (_ppe : ppenv) (x : EcIdent.t) =
  !^ (EcIdent.tostring x)

let pr_local (ppe : ppenv) (x : EcIdent.t) =
  !^ (PPE.loc_symb ppe x)

let pr_funname (ppe : ppenv) (p : EcPath.xpath) =
  !^ (*pr_msymbol*) (PPE.fun_symb ppe p)

let pr_modname (ppe : ppenv) (p : EcPath.mpath) =
  !^ (*pr_msymbol*) (PPE.mod_symb ppe p)

let pr_thname (_ppe : ppenv) (p : EcPath.path) =
  !^ (EcPath.tostring p)

let pr_pv (ppe : ppenv) (x : prog_var) =
  !^ (*pr_msymbol*) (PPE.pv_symb ppe x)

(* -------------------------------------------------------------------- *)

let pr_type (ppe : ppenv) (ty : ty) =
  let rec pr_type btuple (ty : ty) =
    match ty.ty_node with
    | Tglob _m    -> assert false (* FIXME *)
    | Tunivar ui -> pr_univar ppe ui
    | Tvar    a  -> pr_tvar ppe a

    | Ttuple tys ->
        let doc = List.map (pr_type true) tys in
        let doc = seq ~sep:" *" doc in
          if btuple then pr_paren doc else doc

    | Tconstr (name, tyargs) -> begin
        let name = pr_tyname ppe name in
          match tyargs with
          | []      -> name
          | [ty]    -> (pr_type true ty) ^/^ name
          | ty::tys -> 
            pr_paren (
              (^@@^) (pr_type false ty ^^ !^",") ~nest:1 
                (seqc0 (List.map (pr_type false) tys))) ^/^ name
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
      | `Infix `Right, `Right    -> (pi = po) && (fo = `Infix `Right)
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
  let doc = join [dc; !^"?"; d1; !^":"; d2] in
  maybe_paren outer e_bin_prio_if3 doc 
(* -------------------------------------------------------------------- *)

let pr_if_t_e (ppenv : ppenv) pr_sub outer b e1 e2 =
  let dc  = pr_sub ppenv (min_op_prec  , `NonAssoc) b  in
  let d1  = pr_sub ppenv (min_op_prec  , `NonAssoc) e1 in
  let d2  = pr_sub ppenv (e_bin_prio_if, `Right   ) e2 in
  let doc = 
    (join [tk_if; dc; tk_then] ^@@^ d1) ^//^ 
          (tk_else ^@@^ d2) in
  maybe_paren outer e_bin_prio_if doc 
  
let pr_if ppenv pr_sub outer b e1 e2 =
  Pp.group (Pp.ifflat (pr_if3 ppenv pr_sub outer b e1 e2)
              (pr_if_t_e ppenv pr_sub outer b e1 e2)) 


(* -------------------------------------------------------------------- *)
let pr_let (ppenv : ppenv) pr_sub outer pt e1 e2 =
  let ids = lp_ids pt in
  let subppenv = List.fold_left PPE.add_local ppenv ids in

  let dpt = seq (List.map (pr_local subppenv) ids) in

  let d1  = pr_sub ppenv (e_bin_prio_letin, `NonAssoc) e1 in
  let d2  = pr_sub subppenv (e_bin_prio_letin, `NonAssoc) e2 in
  let doc = 
    (^@@^) ~nest:0 
      (join [tk_let; dpt; tk_eq] ^@@^ (d1 ^/^ tk_in))
      d2 in
    maybe_paren outer e_bin_prio_letin doc

(* -------------------------------------------------------------------- *)
let pr_tuple_expr (ppenv : ppenv) pr_sub es =
  let docs = List.map (pr_sub ppenv (min_op_prec, `NonAssoc)) es in
    pr_paren (seq docs)

(* -------------------------------------------------------------------- *)
let pr_op_name (ppenv : ppenv) (p : EcPath.path) =
  pr_qsymbol (PPE.op_symb ppenv p)

(* -------------------------------------------------------------------- *)
let pr_opapp (ppenv : ppenv) pr_sub outer op _tvi es =
  let (nm, opname) = PPE.op_symb ppenv op in
  
  let pr_as_std_op () =
    let (doc, prio) =
      if nm = [] then
        match opname, es with
        | "__nil", [] ->
            (pr_bracket Pp.empty, max_op_prec)

        | "__abs", [e] -> 
            let e = pr_sub ppenv (min_op_prec, `NonAssoc) e in
              (glue [tk_pipe; e; tk_pipe], appprio)

        | "__get", [e1; e2] ->
            let e1 = pr_sub ppenv (e_get_prio , `Left)     e1 in
            let e2 = pr_sub ppenv (min_op_prec, `NonAssoc) e2 in

            let doc = join [e1; pr_bracket e2] in
              (doc, e_get_prio)

        | "__set", [e1; e2; e3] ->
            let e1 = pr_sub ppenv (e_get_prio , `Left    ) e1 in
            let e2 = pr_sub ppenv (min_op_prec, `NonAssoc) e2 in
            let e3 = pr_sub ppenv (min_op_prec, `NonAssoc) e3 in

            let doc = join [e1; pr_bracket (join [e2; tk_larrow; e3])] in
              (doc, e_get_prio)

        | _ ->
            let es = List.map (pr_sub ppenv (appprio, `Right)) es in
              (join ((pr_qsymbol (nm, opname)) :: es), appprio)
      else 
        let es = List.map (pr_sub ppenv (appprio, `Right)) es in
          (join ((pr_qsymbol (nm, opname)) :: es), appprio)
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
              let nest = if opname = "=>" then 0 else 2 in 
              let doc = (^@@^) (d1 ^/^ !^ opname) ~nest d2 in 
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
          Some (glue [tk_flip; tk_tild; e])

    | [e] when qs = EcCoreLib.s_from_int ->
        let e = pr_sub ppenv (max_op_prec, `NonAssoc) e in
          Some (glue [e; tk_from_int])

    | [e1; e2] when qs = EcCoreLib.s_dinter ->
        let e1 = pr_sub ppenv (min_op_prec, `NonAssoc) e1 in
        let e2 = pr_sub ppenv (min_op_prec, `NonAssoc) e2 in
          Some (pr_bracket (glue [e1; tk_dotdot; e2]))

    | _ -> None

  in
    ofdfl pr_as_std_op
      (List.fpick [try_pr_special ;
                   try_pr_as_uniop;
                   try_pr_as_binop])

(* -------------------------------------------------------------------- *)
let pr_locdecl (ppenv : ppenv) (x, ty) =
  let tenv1 = PPE.add_local ppenv x in
  (tenv1, join [pr_local tenv1 x; !^":"; pr_type ppenv ty])

let pr_locdecls (ppenv : ppenv) ds =
    let ppenv, ds = List.map_fold pr_locdecl ppenv ds in
    (ppenv, pr_paren (seq ds))

let pr_expr (ppenv : ppenv) (e : expr) =
  let rec pr_expr (ppenv : ppenv) outer (e : expr) =
    match e.e_node with
    | Evar x ->
        pr_pv ppenv x

    | Elocal x ->
        !^ (EcIdent.name x)

    | Eop (op, _tys) -> (* FIXME infix, prefix, ty_inst *)
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
          e ^^ (pr_paren (seq args))

    | Elet (pt, e1, e2) ->
        pr_let ppenv pr_expr outer pt e1 e2

    | Elam (vardecls, e) ->
      let ppenv, v = pr_locdecls ppenv vardecls in
      (tk_lambda ^/^ v) ^@@^ (pr_expr ppenv (min_op_prec, `NonAssoc) e)
        

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
        pr_paren (seq ps)

  | LvMap (_, x, e, _) ->
      (pr_pv ppenv x) ^^ (pr_bracket (pr_expr ppenv e))

(* -------------------------------------------------------------------- *)
let is_base_instr i = 
  match i.i_node with
  | Sasgn _ | Srnd _ | Scall _ | Sassert _ -> true
  | Sif _ | Swhile _ -> false

let is_base_block s = 
  match s.s_node with
  | [i] -> is_base_instr i
  | _   -> false

let is_empty_block s = s.s_node = []

let rec pr_instr (ppenv : ppenv) (i : instr) =
  let doc =
    match i.i_node with
    | Sasgn (lv, e) ->
      join [pr_lvalue ppenv lv; tk_eq] ^@@^ 
        pr_expr ppenv e

    | Srnd (lv, e) ->
        join [pr_lvalue ppenv lv; tk_eq] ^@@^
          glue [!^"$"; pr_expr ppenv e]

    | Scall (lv, name, args) -> begin
        let doc = 
          let name = pr_funname ppenv name in
          let args = List.map (pr_expr ppenv) args in
            name ^^ (pr_paren (seq args))
        in
        match lv with
        | None    -> doc
        | Some lv -> join [pr_lvalue ppenv lv; !^":=";] ^@@^ doc
    end

    | Sassert e ->
        join [tk_assert; pr_paren (pr_expr ppenv e)]

    | Sif (e, b1, b2) ->
        let e  = pr_paren (pr_expr ppenv e) in
        let b1 = pr_sblock ppenv b1 in
        let b2 = 
          if is_empty_block b2 then []
          else [tk_else; pr_sblock ppenv b2] in
          join ([tk_if; e; b1] @ b2)

    | Swhile (e, body) ->
        let e = pr_paren (pr_expr ppenv e) in
        let body = pr_sblock ppenv body in
          join [tk_while; e; body]

  in
  if is_base_instr i then doc ^^ !^";" else doc

and pr_sblock (ppenv:ppenv) (s:stmt) = 
  if is_base_block s then pr_stmt ppenv s 
  else pr_brace (pr_stmt ppenv s) 

(* -------------------------------------------------------------------- *)
and pr_stmt (ppenv : ppenv) (s : stmt) =
  pr_block (List.map (pr_instr ppenv) s.s_node)

(* -------------------------------------------------------------------- *)
let rec pr_module_item (scope : EcPath.mpath) (ppenv : ppenv) (item : module_item) =
    match item with
    | MI_Variable v ->
      let xpath = EcPath.xpath scope (EcPath.psymbol v.v_name) in
      let doc = pr_modvar ppenv v in
      (PPE.add_pvar ppenv xpath, doc)
        
    | MI_Function f ->
      let xpath = EcPath.xpath scope (EcPath.psymbol f.f_name) in
      let doc = pr_modfun ppenv f in
      (PPE.add_fun ppenv xpath , doc)
        
    | MI_Module me ->
      let scope = EcPath.mqname scope me.me_name in
      let doc = pr_module ppenv (scope, me) in
      (PPE.add_mod ppenv scope, doc)

(* -------------------------------------------------------------------- *)
and pr_modvar (ppenv : ppenv) (v : variable) =
  join [tk_var; !^(v.v_name); !^":"; pr_type ppenv v.v_type]

(* -------------------------------------------------------------------- *)
and pr_modfun (ppenv : ppenv) (f : function_) =
  let fname = f.f_sig.fs_name in
  let fparams, fres = f.f_sig.fs_params, f.f_sig.fs_ret in

  let dparams =
    List.map
      (fun vd -> join [!^(vd.v_name); !^":"; pr_type ppenv vd.v_type])
      fparams in
  let dparams = pr_paren (seq dparams) in

  let prelude =
    join [tk_fun; !^fname ^^ dparams; !^":"; pr_type ppenv fres]
  in

    match f.f_def with
    | FBabs _ -> prelude (* FIXME oracle info *)

    | FBdef def ->
      let dlocals =
          List.map
            (fun vd -> pr_local ppenv (EcIdent.create vd.v_name))
            def.f_locals

      and dbody =
        let bodyppenv =
          List.fold_left
            (fun ppenv x -> PPE.add_local ppenv (EcIdent.create x.v_name))
            ppenv
            ((f.f_sig.fs_params) @ def.f_locals)
        in
        List.map (pr_instr bodyppenv) def.f_body.s_node
      in
      let body = 
        pr_column dlocals ^//^ Pp.empty ^//^ pr_column dbody in
      let body = 
        match def.f_ret with
        | None -> body 
        | Some e -> body ^//^ (tk_return ^@@^ (pr_expr ppenv e ^^ !^";")) in
      join [prelude; tk_eq] ^/^ 
        pr_br_block body


(* -------------------------------------------------------------------- *)
and pr_module (ppenv : ppenv) ((p, m) : EcPath.mpath * module_expr) =
  let mename  = m.me_name in
  let prelude = join [tk_module; !^mename] in
  let moddoc  =

    match m.me_body with
    | ME_Alias m -> 
        join [prelude; tk_eq] ^@@^ 
          pr_modname ppenv m

    | ME_Decl _ ->
        assert false                  (* FIXME *)

    | ME_Structure mstruct ->
        let _, bodydoc =
          List.map_fold (pr_module_item p) ppenv mstruct.ms_body
        in
        join [prelude; tk_eq] ^/^ 
          pr_br_block (pr_column2 bodydoc)
  in
    pr_dotted moddoc

(* -------------------------------------------------------------------- *)
let pr_modtype (_ppenv : ppenv) (_ : module_type) (_:EcPath.Sm.t) =
  Pp.empty                            (* FIXME *)

(* -------------------------------------------------------------------- *)
let pr_typedecl (ppenv : ppenv) ((x, tyd) : EcPath.path * tydecl) =
  let basename = EcPath.basename x in
  let dparams =
    match tyd.tyd_params with
    | []  -> Pp.empty
    | [a] -> pr_tvar ppenv a
    | la  -> pr_paren (seq (List.map (pr_tvar ppenv) la))
  in

  let doc = tk_type ^/^ dparams ^/^ (!^basename) in
  let doc =
    match tyd.tyd_type with
    | None    -> doc
    | Some ty -> (doc ^/^ !^"=") ^@@^ (pr_type ppenv ty)
  in
    pr_dotted doc

(* -------------------------------------------------------------------- *)
let pr_binding (ppenv : ppenv) (x, ty) =
  match ty with
  | GTty ty ->
      let tenv1 = PPE.add_local ppenv x in
        (tenv1, join [pr_local tenv1 x; !^":"; pr_type ppenv ty])

  | GTmem _ ->                          (* FIXME *)
      let ppenv1 = PPE.add_local ppenv x in
        (ppenv1, join [pr_local ppenv1 x; !^":"; tk_memory])

  | GTmodty (p,r) -> (* FIXME print restriction *)
      let ppenv1 = PPE.add_local ppenv x in
        (ppenv1, join [pr_local ppenv1 x; !^":"; pr_modtype ppenv p r])

(* -------------------------------------------------------------------- *)
let pr_bindings (ppenv : ppenv) (b : binding) =
  let ppenv, bs = List.map_fold pr_binding ppenv b in
    ppenv, pr_paren (seq bs)

(* -------------------------------------------------------------------- *)
let tk_quant = function
  | Lforall -> tk_forall
  | Lexists -> tk_exists
  | Llambda -> tk_lambda

(* -------------------------------------------------------------------- *)
let rec pr_form_rec (ppenv : ppenv) outer (f : form) =
  match f.f_node with
  | Fint n ->
    !^ (string_of_int n)
      
  | Flocal id ->
    pr_local ppenv id
      
  | Fpvar (x, i) ->                 (* FIXME *)
      join [pr_pv ppenv x; pr_brace (pr_local ppenv i)]
    
  | Fquant (q, bd, f) ->
    let (subppenv, dd) = pr_bindings ppenv bd in 
    join [tk_quant q; dd^^(!^",")] ^@@^ pr_form_rec subppenv outer f
      
  | Fif (b, f1, f2) ->
    pr_if ppenv pr_form_rec outer b f1 f2
      
  | Flet (lp, f1, f2) ->
    pr_let ppenv pr_form_rec outer lp f1 f2
      
  | Fop(op, _tvi) ->		    (* FIXME infix, prefix, ty_inst *)
    pr_op_name ppenv op
      
  | Fapp ({f_node = Fop (p, tys)}, args) ->
    pr_opapp ppenv pr_form_rec outer p tys args
      
  | Fapp (e, args) ->
    let e    = pr_form_rec ppenv (max_op_prec, `NoneAssoc) e in
    let args = List.map (pr_form_rec ppenv (max_op_prec, `NonAssoc)) args in
    seq ~sep:"" (e::args)
      
  | Ftuple args ->
    pr_tuple_expr ppenv pr_form_rec args
      
  | FhoareF hf ->
    Pp.surround 0 Pp.break1 
      (pr_brace (pr_form ppenv hf.hf_pr)) 
      ( pr_funname ppenv hf.hf_f) 
      (pr_brace (pr_form ppenv hf.hf_po))
      
  | FhoareS hs -> 
    (*let dbody =  (* FIXME : add local program variables ? *)
      let bodyppenv = ppenv in
      List.map (pr_instr bodyppenv) hs.hs_s.s_node
    in *)
    Pp.surround 0 Pp.break1
      (pr_brace (pr_form ppenv hs.hs_pr)) 
      (pr_stmt ppenv hs.hs_s)
      (pr_brace (pr_form ppenv hs.hs_po))
      
  | FequivS es ->
    
    let dbodyl =  (* FIXME : add local program variables ? *)
      let bodyppenv = ppenv in
      List.map (pr_instr bodyppenv) es.es_sl.s_node
    in
    let dbodyr =  (* FIXME : add local program variables ? *)
      let bodyppenv = ppenv in
      List.map (pr_instr bodyppenv) es.es_sr.s_node
    in
    join [
      !^ "equiv";
      pr_bracket (
        join [
          pr_mblocks [dbodyl];
          !^ "~";
          pr_mblocks [dbodyr];
          !^ ":";
          pr_form_rec ppenv outer es.es_pr;
          !^ "==>";
          pr_form_rec ppenv outer es.es_po;
        ] ) ]

  | Fpr (m, f, args, event) ->
      join [
        !^ "Pr";
        pr_bracket (
          join [
            pr_funname ppenv f;
            pr_paren (join (List.map (pr_form_rec ppenv outer) args));
            !^ "@";
            pr_ident ppenv m;
            !^ ":";
            pr_form_rec ppenv outer event
          ])]

  | FequivF eqv ->
      join [
        !^ "equiv";
        pr_bracket (
          join [
            pr_funname ppenv eqv.ef_fl;
            !^ "~";
            pr_funname ppenv eqv.ef_fr;
            !^ ":";
            pr_form_rec ppenv outer eqv.ef_pr;
            !^ "==>";
            pr_form_rec ppenv outer eqv.ef_po ])]

  | Fglob (mp,m) ->
    join [
      pr_paren (join [!^ "glob"; pr_modname ppenv mp]);
      pr_brace (pr_local ppenv m) ]

and pr_form ppenv f = pr_form_rec ppenv (min_op_prec, `NonAssoc) f


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
    pr_bracket (join (List.map (pr_tvar ppenv) ids))

let pr_opdecl (ppenv : ppenv) ((x, op) : EcPath.path * operator) =
  let basename = EcPath.basename x in

  let dop, ddecl =
    match op.op_kind with
    | OB_oper i ->
      let ddecl =
        match i with
        | None -> join [!^":"; pr_type ppenv (op_ty op)]
        | Some e ->
          let vardecls, e =
            match e.e_node with
            | Elam (vardecls,e) -> vardecls, e
            | _ -> [], e in
          let subppenv, dd = 
            if vardecls = [] then ppenv, Pp.empty 
            else pr_locdecls ppenv vardecls in
          join [
            dd; !^":"; pr_type ppenv e.e_ty;
            !^"="] ^@@^ pr_expr subppenv e in
      (tk_op, ddecl)

    | OB_pred i ->
      let ddecl =
        match i with
        | None -> join [!^":"; pr_type ppenv (op_ty op)]
        | Some f ->
          let vardecls, f =
            match f.f_node with
            | Fquant(Llambda,vardecls,f) -> vardecls, f
            | _ -> [], f in
          let vardecls = List.map (fun (x,t) -> x,EcFol.destr_gty t) vardecls in
          let subppenv, dd = pr_locdecls ppenv vardecls in
          join [dd; !^"="; pr_form subppenv f] in
      tk_pred, ddecl in

  let doc =
    join [dop; !^basename; pr_tyvarsdecl ppenv op.op_tparams; ddecl]
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
    match ax.ax_tparams with
    | [] -> !^basename
    | _  -> 
        let args = List.map (pr_ident ppenv) ax.ax_tparams in
          !^basename ^^ (pr_angle (seq args))

  and spec =
    match ax.ax_spec with
    | None   -> !^"<why3-imported>"
    | Some f -> pr_form ppenv f
  in

    pr_dotted (join [tk; pr_name; !^":"; spec])

(* -------------------------------------------------------------------- *)
let pr_modsig (_ppenv : ppenv) ((x, _tymod) : EcPath.path * module_sig) =
  let basename = EcPath.basename x in
    pr_dotted (join [tk_module; tk_type; !^basename; !^"="])

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
    let mp = EcPath.mpath_crt (xpath m.me_name) [] None in
    let doc = pr_module ppenv (mp, m) in
    (PPE.add_mod ppenv mp, doc)

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
        join [tk_type; pr_ident ppenv x; !^"="; pr_type ppenv ty]
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
            let pext = [tk_with; (seq pext)] in
              doc @ pext
        in
          join doc

    | CTh_struct cstruct ->
        let basename = EcPath.basename name in
        let _, pr_cstruct =
          List.map_fold (pr_ctheory_item name) ppenv cstruct
        in
       pr_dotted (tk_theory ^/^ !^basename) ^^
        (Pp.nest 2 (Pp.break0 ^^ pr_column2 (pr_cstruct))) ^^ Pp.break0 ^^
         pr_dotted (tk_end    ^/^ !^basename)

(* -------------------------------------------------------------------- *)
let pp_path (fmt : Format.formatter) (p : EcPath.path) =
  Format.fprintf fmt "%s" (EcPath.tostring p)

let fmtpretty = 
  Pprint.Formatter.pretty 0.8 80

let pp_type (ppenv : EcEnv.env) (fmt : Format.formatter) ty =
  fmtpretty fmt (pr_type (empty ppenv) ty)

let pp_form (ppenv : EcEnv.env) (fmt : Format.formatter) (f : form) =
  fmtpretty fmt (pr_form (empty ppenv) f)

let pretty stream doc =
  Pprint.Channel.pretty 0.8 80 stream doc
