(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcModules
open EcDecl
open EcFol

module P  = EcPath
module EP = EcParser

(* -------------------------------------------------------------------- *)
type 'a pp = Format.formatter -> 'a -> unit

(* -------------------------------------------------------------------- *)
module PPEnv = struct
  type t = {
    ppe_env   : EcEnv.env;
    ppe_scope : EcPath.xpath option;
  }

  let ofenv (env : EcEnv.env) =
    { ppe_env   = env;
      ppe_scope = None; }

  let tyvar (_ : t) x =
    EcIdent.tostring x

  let enter ppe scope =
    { ppe with ppe_scope = Some scope; }

  let enter_by_memid ppe id =
    match EcEnv.Memory.byid id ppe.ppe_env with
    | None   -> ppe
    | Some m -> enter ppe (EcMemory.xpath m)

  let add_local x _ = x

  let p_shorten cond p =
    let rec shorten prefix (nm, x) =
      match cond (nm, x) with
      | true  -> (nm, x)
      | false -> begin
        match prefix with
        | [] -> (nm, x)
        | n :: prefix -> shorten prefix (n :: nm, x)
      end
    in
    
    let (nm, x) = P.toqsymbol p in
    let (nm, x) = shorten (List.rev nm) ([], x) in
      (nm, x)

  let ty_symb (ppe : t) p = 
      let exists sm =
      try  EcPath.p_equal (EcEnv.Ty.lookup_path sm ppe.ppe_env) p
      with EcEnv.LookupFailure _ -> false
    in
      p_shorten exists p

  let op_symb (ppe : t) p =
    let exists sm =
      try  EcPath.p_equal (EcEnv.Op.lookup_path sm ppe.ppe_env) p
      with EcEnv.LookupFailure _ -> false
    in
      p_shorten exists p

  let rec mod_symb (ppe : t) mp : EcSymbols.msymbol =
    match mp.P.m_top with
    | `Abstract x ->
        [EcIdent.name x, []]

    | `Concrete (p1, p2) ->
        let exists sm =
          match EcEnv.Mod.sp_lookup_opt sm ppe.ppe_env with
          | None -> false
          | Some (mp1, _) -> P.mt_equal mp1.P.m_top mp.P.m_top
        in

        let rec shorten prefix (nm, x) =
          match exists (nm, x) with
          | true  -> (nm, x)
          | false -> begin
              match prefix with
              | [] -> (nm, x)
              | n :: prefix -> shorten prefix (n :: nm, x)
          end
        in

        let (nm, x) = P.toqsymbol p1 in
        let (nm, x) = shorten (List.rev nm) ([], x) in

        let msymb =
            (List.map (fun x -> (x, [])) nm)
          @ [(x, List.flatten (List.map (mod_symb ppe) mp.P.m_args))]
          @ (List.map (fun x -> (x, [])) (odfl [] (omap p2 P.tolist)))
        in
          msymb

  let rec modtype_symb (ppe : t) mty =
    let exists sm =
      match EcEnv.ModTy.lookup_opt sm ppe.ppe_env with
      | None -> false
      | Some (p, _) -> P.p_equal p mty.mt_name
    in

    let rec shorten prefix (nm, x) =
      match exists (nm, x) with
      | true  -> (nm, x)
      | false -> begin
          match prefix with
          | [] -> (nm, x)
          | m :: prefix -> shorten prefix (m :: nm, x)
      end
    in

    let (nm, x) = P.toqsymbol mty.mt_name in
    let (nm, x) = shorten (List.rev nm) ([], x) in

    let msymb =
        (List.map (fun x -> (x, [])) nm)
      @ [(x, List.flatten (List.map (mod_symb ppe) mty.mt_args))]
    in
      msymb

end

(* -------------------------------------------------------------------- *)
let pp_id pp fmt x = Format.fprintf fmt "%a" pp x

(* -------------------------------------------------------------------- *)
let pp_if c pp1 pp2 fmt x =
  match c with
  | true  -> pp1 fmt x
  | false -> pp2 fmt x

(* -------------------------------------------------------------------- *)
let pp_maybe c tx pp fmt x =
  pp_if c (tx pp) pp fmt x

(* -------------------------------------------------------------------- *)
let rec pp_list sep pp fmt xs =
  let pp_list = pp_list sep pp in
    match xs with
    | []      -> ()
    | [x]     -> Format.fprintf fmt "%a" pp x
    | x :: xs -> Format.fprintf fmt "%a%(%)%a" pp x sep pp_list xs

(* -------------------------------------------------------------------- *)
let pp_enclose ~pre ~post pp fmt x =
  Format.fprintf fmt "%(%)%a%(%)" pre pp x post

(* -------------------------------------------------------------------- *)
let pp_paren pp fmt x =
  pp_enclose "(" ")" pp fmt x

(* -------------------------------------------------------------------- *)
let pp_maybe_paren c pp =
  pp_maybe c pp_paren pp

(* -------------------------------------------------------------------- *)
let pp_string fmt x =
  Format.fprintf fmt "%s" x

(* -------------------------------------------------------------------- *)
let pp_path fmt p =
  Format.fprintf fmt "%s" (P.tostring p)

(* -------------------------------------------------------------------- *)
let pp_topmod ppe fmt p =
  Format.fprintf fmt "%a"
    EcSymbols.pp_msymbol (PPEnv.mod_symb ppe p)

(* -------------------------------------------------------------------- *)
let pp_tyvar ppe fmt x =
  Format.fprintf fmt "%s" (PPEnv.tyvar ppe x)

(* -------------------------------------------------------------------- *)
let pp_tyunivar _ppe fmt x =
  Format.fprintf fmt "#%d" x

(* -------------------------------------------------------------------- *)
let pp_tyname ppe fmt p =
  Format.fprintf fmt "%a" EcSymbols.pp_qsymbol (PPEnv.ty_symb ppe p)

(* -------------------------------------------------------------------- *)
let pp_funname (ppe : PPEnv.t) fmt p =
  Format.fprintf fmt "%a.%a"
    (pp_topmod ppe) p.P.x_top pp_path p.P.x_sub

(* -------------------------------------------------------------------- *)
let pp_pv (ppe : PPEnv.t) fmt p =
  let k = p.pv_kind in
  let p = p.pv_name in

  let inscope =
    match ppe.PPEnv.ppe_scope with
    | None    -> false
    | Some xp -> P.x_equal p (P.xqname xp (P.basename p.P.x_sub))
  in

  match k with
  | PVloc when inscope ->
      Format.fprintf fmt "%s" (P.basename p.P.x_sub)

  | _ ->
      Format.fprintf fmt "%a.%a"
        (pp_topmod ppe) p.P.x_top pp_path p.P.x_sub

(* -------------------------------------------------------------------- *)
let pp_modtype (ppe : PPEnv.t) fmt ((mty, _) : module_type * _) =
  Format.fprintf fmt "%a"
    EcSymbols.pp_msymbol (PPEnv.modtype_symb ppe mty)

(* -------------------------------------------------------------------- *)
let pp_local (_ppe : PPEnv.t) fmt x =
  Format.fprintf fmt "%s" (EcIdent.name x)

(* -------------------------------------------------------------------- *)
let rec pp_type_r ppe btuple fmt ty =
  match ty.ty_node with
  | Tglob m -> Format.fprintf fmt "(glob %a)" (pp_topmod ppe) m

  | Tunivar x -> pp_tyunivar ppe fmt x
  | Tvar    x -> pp_tyvar ppe fmt x

  | Ttuple tys ->
      pp_maybe_paren btuple
        (pp_list " *@ " (pp_type_r ppe true)) fmt tys

  | Tconstr (name, tyargs) -> begin
      match tyargs with
      | [] ->
          pp_tyname ppe fmt name

      | [x] ->
          Format.fprintf fmt "%a %a"
            (pp_type_r ppe true) x (pp_tyname ppe) name

      | xs ->
          Format.fprintf fmt "%a %a"
            (pp_paren (pp_list ",@ " (pp_type_r ppe false))) xs
            (pp_tyname ppe) name
    end

  | Tfun (t1, t2) ->
      Format.fprintf fmt "%a ->@ %a"
        (pp_type_r ppe true) t1 (pp_type_r ppe false) t2

let pp_type ppe fmt ty =
  pp_type_r ppe true fmt ty

(* -------------------------------------------------------------------- *)
type assoc  = [`Left | `Right | `NonAssoc]
type fixity = [`Prefix | `Postfix | `Infix of assoc]
type opprec = int * fixity

(* -------------------------------------------------------------------- *)
let maybe_paren (outer, side) inner pp =
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
    pp_maybe_paren (not (noparens inner outer side)) pp

(* -------------------------------------------------------------------- *)
let e_bin_prio_impl   = (10, `Infix `Right)
let e_bin_prio_if     = (15, `Prefix)
let e_bin_prio_if3    = (17, `Infix `NonAssoc)
let e_bin_prio_letin  = (19, `Prefix)
let e_bin_prio_or     = (20, `Infix `Right)
let e_bin_prio_and    = (25, `Infix `Right)
let e_bin_prio_eq     = (27, `Infix `NonAssoc)
let e_bin_prio_op1    = (30, `Infix `Left)
let e_bin_prio_op2    = (40, `Infix `Left)
let e_bin_prio_op3    = (50, `Infix `Left)
let e_bin_prio_op4    = (60, `Infix `Left)

let e_uni_prio_not    =  26
let e_uni_prio_uminus = 500
let appprio           = (10000, `Infix `NonAssoc)
let e_get_prio        = (20000, `Infix `Left)

let min_op_prec = (-1     , `Infix `NonAssoc)
let max_op_prec = (max_int, `Infix `NonAssoc)

(* -------------------------------------------------------------------- *)
let priority_of_binop name =
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
  | Some EP.ADD   -> Some e_bin_prio_op2
  | Some EP.MINUS -> Some e_bin_prio_op2
  | Some EP.OP3 _ -> Some e_bin_prio_op3
  | Some EP.STAR  -> Some e_bin_prio_op3
  | Some EP.OP4 _ -> Some e_bin_prio_op4

  | _ -> None

(* -------------------------------------------------------------------- *)
let priority_of_unop name =
  match EcIo.lex_single_token name with
  | Some EP.NOT   -> Some e_uni_prio_not
  | Some EP.EQ    -> Some e_uni_prio_uminus
  | Some(EP.AND _)-> Some e_uni_prio_uminus  
  | Some(EP.OR _) -> Some e_uni_prio_uminus  
  | Some EP.STAR  -> Some e_uni_prio_uminus  
  | Some EP.ADD   -> Some e_uni_prio_uminus  
  | Some EP.MINUS -> Some e_uni_prio_uminus  
  | Some EP.GT    -> Some e_uni_prio_uminus  
  | Some EP.OP1 _ -> Some e_uni_prio_uminus 
  | Some EP.OP2 _ -> Some e_uni_prio_uminus
  | Some EP.OP3 _ -> Some e_uni_prio_uminus
  | Some EP.OP4 _ -> Some e_uni_prio_uminus
  | _             -> None

(* -------------------------------------------------------------------- *)
let is_unop name = 
  (priority_of_unop name) <> None

let is_binop name =
  (priority_of_binop name) <> None

let is_unbinop name = is_unop name || is_binop name
  
(* -------------------------------------------------------------------- *)
let pp_if3 (ppe : PPEnv.t) pp_sub outer fmt (b, e1, e2) =
  let pp fmt (b, e1, e2)=
    Format.fprintf fmt "@[<hov 2>%a@ ? %a@ : %a@]"
      (pp_sub ppe (e_bin_prio_if3, `Left )) b
      (pp_sub ppe (min_op_prec, `NonAssoc)) e1
      (pp_sub ppe (e_bin_prio_if3, `Right)) e2
  in
    maybe_paren outer e_bin_prio_if3 pp fmt (b, e1, e2)

(* -------------------------------------------------------------------- *)
let pp_let (ppe : PPEnv.t) pp_sub outer fmt (pt, e1, e2) =
  let pp fmt (pt, e1, e2) =
    let ids    = lp_ids pt in
    let subppe = List.fold_left PPEnv.add_local ppe ids in
      Format.fprintf fmt "@[<hov 0>let %a =@;<1 2> [@%a@]@ in@ %a@]"
        (pp_list ", " (pp_local ppe)) ids
        (pp_sub ppe (e_bin_prio_letin, `NonAssoc)) e1
        (pp_sub subppe (e_bin_prio_letin, `NonAssoc)) e2
  in
    maybe_paren outer e_bin_prio_letin pp fmt (pt, e1, e2)

(* -------------------------------------------------------------------- *)
let pp_tuple (ppe : PPEnv.t) pp_sub es =
  pp_paren (pp_list ",@ " (pp_sub ppe (min_op_prec, `NonAssoc))) es

(* -------------------------------------------------------------------- *)
let pp_opname_as_operator fmt (nm, op) =
  match nm with
  | [] -> 
    Format.fprintf fmt "%s" op
  | _  ->
      let op = Printf.sprintf "( %s )" op in
        EcSymbols.pp_qsymbol fmt (nm, op)

let pp_opapp (ppe : PPEnv.t) pp_sub outer fmt (op, _tvi, es) =
  let (nm, opname) = PPEnv.op_symb ppe op in

  let pp_as_std_op fmt =
    let pp_stdapp fmt =
      match es with
      | [] -> EcSymbols.pp_qsymbol fmt (nm, opname)
      | _  ->
          Format.fprintf fmt "@[<hov 2>%a@ %a@]"
            EcSymbols.pp_qsymbol (nm, opname)
            (pp_list "@ " (pp_sub ppe (appprio, `Right))) es
    in

    let (pp, prio) =
      if nm = [] then
        match opname, es with
        | "__nil", [] ->
            ((fun fmt -> pp_string fmt "[]"), max_op_prec)

        | "__abs", [e] ->
            let pp fmt =
              Format.fprintf fmt "`|%a|"
                (pp_sub ppe (min_op_prec, `NonAssoc)) e
            in
              (pp, appprio)

        | "__get", [e1; e2] ->
            let pp fmt =
              Format.fprintf fmt "@[%a.[%a]@]"
                (pp_sub ppe (e_get_prio, `Left)) e1
                (pp_sub ppe (min_op_prec, `NonAssoc)) e2
            in
              (pp, e_get_prio)

        | "__set", [e1; e2; e3] ->
            let pp fmt =
              Format.fprintf fmt "@[%a.[%a <- %a]@]"
                (pp_sub ppe (e_get_prio , `Left    )) e1
                (pp_sub ppe (min_op_prec, `NonAssoc)) e2
                (pp_sub ppe (min_op_prec, `NonAssoc)) e3
            in
              (pp, e_get_prio)

        | _ ->
            (pp_stdapp, if es = [] then max_op_prec else appprio)
      else 
        (pp_stdapp, appprio)
    in
      maybe_paren outer prio (fun fmt () -> pp fmt) fmt

  and try_pp_as_uniop () =
    match es with
    | [e] -> 
      if nm = [] then 
        begin match priority_of_unop opname with
        | None -> None
        | Some opprio  ->
            let opprio = (opprio, `Prefix) in
            let pp fmt =
              Format.fprintf fmt "@[%a@ %a@]"
                pp_opname_as_operator (nm, opname)
                (pp_sub ppe (opprio, `NonAssoc)) e in
            let pp fmt =
              maybe_paren outer opprio (fun fmt () -> pp fmt) fmt
            in
              Some pp
        end
      else None
    | _ -> None

  and try_pp_as_binop () =
    match es with
    | [e1; e2] ->
      if nm = [] then 
        begin match priority_of_binop opname with
        | None -> None
        | Some opprio ->
            let pp fmt =
              Format.fprintf fmt "@[%a %a@ %a@]"
                (pp_sub ppe (opprio, `Left)) e1
                pp_opname_as_operator (nm, opname)
                (pp_sub ppe (opprio, `Right)) e2 in
            let pp fmt =
              maybe_paren outer opprio (fun fmt () -> pp fmt) fmt
            in
              Some pp
        end
      else None

    | _ -> None
        
  and try_pp_special () = 
    let qs = P.toqsymbol op in
    match es with
    | [] when qs = EcCoreLib.s_dbool ->
        Some (fun fmt () -> pp_string fmt "{0,1}")

    | [e] when qs = EcCoreLib.s_dbitstring ->
        let pp fmt () =
          Format.fprintf fmt "{0,1}~%a"
            (pp_sub ppe (max_op_prec, `NonAssoc)) e
        in
          Some pp

    | [e] when qs = EcCoreLib.s_from_int ->
        let pp fmt () =
          Format.fprintf fmt "%a%%r"
            (pp_sub ppe (max_op_prec, `NonAssoc)) e
        in
          Some pp

    | [e1; e2] when qs = EcCoreLib.s_dinter ->
        let pp fmt () =
          Format.fprintf fmt "[%a..%a]"
            (pp_sub ppe (min_op_prec, `NonAssoc)) e1
            (pp_sub ppe (min_op_prec, `NonAssoc)) e2
        in
          Some pp

    | _ -> None

  in
    (odfl
       pp_as_std_op
       (List.fpick [try_pp_special ;
                    try_pp_as_uniop;
                    try_pp_as_binop])) fmt ()

(* --------------------------------------------------------------------  *)
let pp_locbind (ppe : PPEnv.t) (x, ty) =
  let tenv1  = PPEnv.add_local ppe x in
  let pp fmt =
    Format.fprintf fmt "(%a : %a)"
      (pp_local tenv1) x (pp_type  ppe) ty
  in
    (tenv1, pp)

(* -------------------------------------------------------------------- *)
let rec pp_locbinds ppe vs =
  match vs with
  | [] ->
      (ppe, fun _ -> ())
  | [v] ->
      let ppe, pp = pp_locbind ppe v in
        (ppe, fun fmt -> Format.fprintf fmt "%t" pp)
  | v :: vs ->
      let ppe, pp1 = pp_locbind  ppe v  in
      let ppe, pp2 = pp_locbinds ppe vs in
        (ppe, fun fmt -> Format.fprintf fmt "%t@ %t" pp1 pp2)

(* -------------------------------------------------------------------- *)
let pp_expr (ppe : PPEnv.t) fmt (e : expr) =
  let rec pp_expr (ppe : PPEnv.t) outer fmt (e : expr) =
    match e.e_node with
    | Eint i ->
        Format.fprintf fmt "%d" i

    | Evar x ->
        pp_pv ppe fmt x

    | Elocal x ->
        pp_local ppe fmt x

    | Eop (op, tys) ->
        pp_opapp ppe pp_expr outer fmt (op, tys, [])

    | Eif (c, e1, e2) ->
        pp_if3 ppe pp_expr outer fmt (c, e1, e2)

    | Etuple es ->
        pp_tuple ppe pp_expr fmt es

    | Eapp ({e_node = Eop (op, tys) }, args) ->
        pp_opapp ppe pp_expr outer fmt (op, tys, args)

    | Eapp (e, args) -> 
        pp_list "@ "
          (pp_expr ppe (max_op_prec, `NonAssoc)) fmt
          (e :: args)

    | Elet (pt, e1, e2) ->
        pp_let ppe pp_expr outer fmt (pt, e1, e2)

    | Elam (vardecls, e) ->
        let (subppe, pp) = pp_locbinds ppe vardecls in
          Format.fprintf fmt "lambda %t,@ %a"
            pp (pp_expr subppe (min_op_prec, `NonAssoc)) e

  in
    pp_expr ppe (min_op_prec, `NonAssoc) fmt e

(* -------------------------------------------------------------------- *)
let pp_lvalue (ppe : PPEnv.t) fmt lv =
  match lv with
  | LvVar (p, _) ->
      pp_pv ppe fmt p

  | LvTuple ps ->
      pp_paren (pp_list ", " (pp_pv ppe)) fmt (List.map fst ps)

  | LvMap (_, x, e, _) ->
      Format.fprintf fmt "%a[%a]"
        (pp_pv ppe) x (pp_expr ppe) e

(* -------------------------------------------------------------------- *)
let pp_instr_for_form (ppe : PPEnv.t) fmt i =
  match i.i_node with
  | Sasgn (lv, e) ->
      Format.fprintf fmt "%a =@ %a"
        (pp_lvalue ppe) lv (pp_expr ppe) e

  | Srnd (lv, e) ->
      Format.fprintf fmt "%a =$@ [<hov 2>%a@]"
        (pp_lvalue ppe) lv (pp_expr ppe) e

  | Scall (None, xp, args) ->
      Format.fprintf fmt "%a(%a)"
        (pp_funname ppe) xp
        (pp_list ",@ " (pp_expr ppe)) args

  | Scall (Some lv, xp, args) ->
      Format.fprintf fmt "%a :=@ %a(%a)"
        (pp_lvalue ppe) lv
        (pp_funname ppe) xp
        (pp_list ",@ " (pp_expr ppe)) args

  | Sassert e ->
      Format.fprintf fmt "assert (%a)"
        (pp_expr ppe) e

  | Swhile (e, _) ->
      Format.fprintf fmt "while (%a) {...}"
        (pp_expr ppe) e

  | Sif (e, _, _) ->
      Format.fprintf fmt "if (%a) {...}"
        (pp_expr ppe) e

(* -------------------------------------------------------------------- *)
let pp_stmt_for_form (ppe : PPEnv.t) fmt (s : stmt) =
  match s.s_node with
  | [] ->
      pp_string fmt "<skip>"

  | [i] ->
      pp_instr_for_form ppe fmt i

  | [i1; i2] ->
      Format.fprintf fmt "%a;@ %a"
        (pp_instr_for_form ppe) i1
        (pp_instr_for_form ppe) i2

  | _ ->
      let i1 = List.hd s.s_node in
      let i2 = List.hd (List.rev s.s_node) in
        Format.fprintf fmt "%a;@ ...;@ %a"
          (pp_instr_for_form ppe) i1
          (pp_instr_for_form ppe) i2

(* -------------------------------------------------------------------- *)
let string_of_quant = function
  | Lforall -> "forall"
  | Lexists -> "exists"
  | Llambda -> "lambda"

(* -------------------------------------------------------------------- *)
let pp_binding (ppe : PPEnv.t) (x, ty) =
  match ty with
  | GTty ty ->
      let tenv1  = PPEnv.add_local ppe x in
      let pp fmt =
        Format.fprintf fmt "(%a : %a)"
          (pp_local tenv1) x (pp_type  ppe) ty
      in
        (tenv1, pp)

  | GTmem _ ->
      let tenv1  = PPEnv.add_local ppe x in
      let pp fmt =
        Format.fprintf fmt "(%a : memory)" (pp_local tenv1) x
      in
        (tenv1, pp)

  | GTmodty (p, sm) ->
      let tenv1  = PPEnv.add_local ppe x in
      let pp fmt =
        Format.fprintf fmt "(%a <: %a)"
          (pp_local tenv1) x (pp_modtype ppe) (p, sm)
      in
        (tenv1, pp)

(* -------------------------------------------------------------------- *)
let rec pp_bindings ppe bds =
  match bds with
  | [] ->
      (ppe, fun _ -> ())
  | [bd] ->
      let ppe, pp = pp_binding ppe bd in
        (ppe, fun fmt -> Format.fprintf fmt "%t" pp)
  | bd :: bds ->
      let ppe, pp1 = pp_binding  ppe bd  in
      let ppe, pp2 = pp_bindings ppe bds in
        (ppe, fun fmt -> Format.fprintf fmt "%t@ %t" pp1 pp2)

(* -------------------------------------------------------------------- *)
let rec pp_form_r (ppe : PPEnv.t) outer fmt f =
  match f.f_node with
  | Fint n ->
      Format.fprintf fmt "%d" n
      
  | Flocal id ->
      pp_local ppe fmt id
      
  | Fpvar (x, i) ->
      let ppe = PPEnv.enter_by_memid ppe i in
        Format.fprintf fmt "%a{%a}" (pp_pv ppe) x (pp_local ppe) i
    
  | Fquant (q, bd, f) ->
      let (subppe, pp) = pp_bindings ppe bd in
        Format.fprintf fmt "@[<hov 2>%s %t,@ %a@]"
          (string_of_quant q) pp (pp_form_r subppe outer) f

  | Fif (b, f1, f2) ->
      pp_if3 ppe pp_form_r outer fmt (b, f1, f2)
      
  | Flet (lp, f1, f2) ->
      pp_let ppe pp_form_r outer fmt (lp, f1, f2)
      
  | Fop (op, tvi) ->
      pp_opapp ppe pp_form_r outer fmt (op, tvi, [])
      
  | Fapp ({f_node = Fop (p, tys)}, args) ->
      pp_opapp ppe pp_form_r outer fmt (p, tys, args)
      
  | Fapp (e, args) ->
      pp_list "@ "
        (pp_form_r ppe (max_op_prec, `NonAssoc)) fmt
        (e :: args)
      
  | Ftuple args ->
      pp_tuple ppe pp_form_r fmt args
      
  | FhoareF hf ->
      Format.fprintf fmt "hoare[@[<hov 2>%a :@\n%a@ ==> @[<hov 2>%a@]@]]"
        (pp_funname ppe) hf.hf_f
        (pp_form_r ppe (max_op_prec, `NonAssoc)) hf.hf_pr
        (pp_form_r ppe (max_op_prec, `NonAssoc)) hf.hf_po
      
  | FhoareS hs -> 
      Format.fprintf fmt "hoare[@[<hov 2>%a :@\n%a@ ==> @[<hov 2>%a@]@]]"
        (pp_stmt_for_form ppe) hs.hs_s
        (pp_form_r ppe (max_op_prec, `NonAssoc)) hs.hs_pr
        (pp_form_r ppe (max_op_prec, `NonAssoc)) hs.hs_po

  | FequivF eqv ->
      Format.fprintf fmt "equiv[@[<hov 2>%a ~ %a :@\n%a@ ==> @[<hov 2>%a@]@]]"
        (pp_funname ppe) eqv.ef_fl
        (pp_funname ppe) eqv.ef_fr
        (pp_form_r ppe (max_op_prec, `NonAssoc)) eqv.ef_pr
        (pp_form_r ppe (max_op_prec, `NonAssoc)) eqv.ef_po
      
  | FequivS es ->
      Format.fprintf fmt "equiv[@[<hov 2>%a ~ %a :@\n%a@ ==> @[<hov 2>%a@]@]]"
        (pp_stmt_for_form ppe) es.es_sl
        (pp_stmt_for_form ppe) es.es_sr
        (pp_form_r ppe (max_op_prec, `NonAssoc)) es.es_pr
        (pp_form_r ppe (max_op_prec, `NonAssoc)) es.es_po

  | Fglob (mp, me) ->
      Format.fprintf fmt "(glob %a){%a}" (pp_topmod ppe) mp (pp_local ppe) me

  | Fpr _ ->
      Format.fprintf fmt "Fpr[to-be-done]"

  | FbdHoareF _ ->
      Format.fprintf fmt "PHoareF[to-be-done]"

  | FbdHoareS _ ->
      Format.fprintf fmt "PHoareS[to-be-done]"

and pp_form ppe fmt f =
  pp_form_r ppe (min_op_prec, `NonAssoc) fmt f

(* -------------------------------------------------------------------- *)
let pp_typedecl (ppe : PPEnv.t) fmt (x, tyd) =
  let name = P.basename x in

  let pp_prelude fmt =
    match tyd.tyd_params with
    | [] ->
        Format.fprintf fmt "type %s" name

    | [tx] ->
        Format.fprintf fmt "type %a %s"
          (pp_tyvar ppe) tx name

    | txs ->
        Format.fprintf fmt "type (%a) %s"
          (pp_paren (pp_list ",@ " (pp_tyvar ppe))) txs name

  and pp_body fmt =
    match tyd.tyd_type with
    | None    -> ()
    | Some ty -> Format.fprintf fmt " =@ %a" (pp_type_r ppe false) ty

  in
    Format.fprintf fmt "%t%t.@\n" pp_prelude pp_body

(* -------------------------------------------------------------------- *)
let pp_tyvarannot (ppe : PPEnv.t) fmt ids =
  match ids with
  | [] -> ()
  | _  -> Format.fprintf fmt "<%a>" (pp_list ",@ " (pp_tyvar ppe)) ids

(* -------------------------------------------------------------------- *)
let pp_opdecl_pr (ppe : PPEnv.t) fmt (x, ts, ty, op) =
  let basename = P.basename x in

  let pp_body fmt =
    match op with
    | None ->
        Format.fprintf fmt " : %a" (pp_type_r ppe false) ty

    | Some f ->
        let ((subppe, pp_vds), f) =
          let (vds, f) =
            match f.f_node with
            | Fquant (Llambda, vds, f) -> (vds, f)
            | _ -> ([], f) in

          let vds = List.map (sndmap EcFol.destr_gty) vds in
            (pp_locbinds ppe vds, f)
        in
          Format.fprintf fmt "%t = %a" pp_vds (pp_form subppe) f
  in
    Format.fprintf fmt "pred %s%a%t.@\n"
      basename (pp_tyvarannot ppe) ts pp_body

let pp_opdecl_op (_ppe : PPEnv.t) _fmt (_x, _ts, _ty, _op) =
  assert false

let pp_opdecl (ppe : PPEnv.t) fmt (x, op) =
  match op.op_kind with
  | OB_oper i -> pp_opdecl_op ppe fmt (x, op.op_tparams, op_ty op, i)
  | OB_pred i -> pp_opdecl_pr ppe fmt (x, op.op_tparams, op_ty op, i)

(* -------------------------------------------------------------------- *)
let string_of_axkind = function
  | Axiom   -> "axiom"
  | Lemma _ -> "lemma"

let pp_axiom (ppe : PPEnv.t) fmt (x, ax) =
  let basename = P.basename x in

  let pp_spec fmt =
    match ax.ax_spec with
    | None   -> pp_string fmt "<why3-imported>"
    | Some f -> pp_form ppe fmt f

  and pp_name fmt =
    match ax.ax_tparams with
    | [] -> pp_string fmt basename
    | ts ->
        Format.fprintf fmt "%s <%a>" basename
          (pp_list ",@ " (pp_tyvar ppe)) ts
  in
    Format.fprintf fmt "%s %t : %t.@\n"
      (string_of_axkind ax.ax_kind) pp_name pp_spec

(* -------------------------------------------------------------------- *)
type ppnode1 = [
  | `Asgn   of (EcModules.lvalue * EcTypes.expr)
  | `Assert of (EcTypes.expr)
  | `Call   of (EcModules.lvalue option * P.xpath * EcTypes.expr list)
  | `Rnd    of (EcModules.lvalue * EcTypes.expr)
  | `If     of (EcTypes.expr)
  | `Else
  | `While  of (EcTypes.expr)
  | `None
  | `EBlk
]

type ppnode = ppnode1 * ppnode1 * [`P | `Q | `B] * ppnode list list

type cppnode1 = string list
type cppnode  = cppnode1 * cppnode1 * char * cppnode list list

let at n i =
  match i, n with
  | Sasgn (lv, e)    , 0 -> Some (`Asgn (lv, e)    , `P, [])
  | Srnd  (lv, e)    , 0 -> Some (`Rnd  (lv, e)    , `P, [])
  | Scall (lv, f, es), 0 -> Some (`Call (lv, f, es), `P, [])
  | Sassert e        , 0 -> Some (`Assert e        , `P, [])

  | Swhile (e, s), 0 -> Some (`While e, `P, s.s_node)
  | Swhile _     , 1 -> Some (`EBlk   , `B, [])

  | Sif (e, s, _ ), 0 -> Some (`If e, `P, s.s_node)
  | Sif (_, _, s ), 1 -> begin
      match s.s_node with
      | [] -> Some (`EBlk, `B, [])
      | _  -> Some (`Else, `Q, s.s_node)
    end

  | Sif (_, _, s), 2 -> begin
      match s.s_node with
      | [] -> None
      | _  -> Some (`EBlk, `B, [])
    end

  | _, _ -> None

let rec collect2_i i1 i2 : ppnode list =
  let rec doit n =
    match obind i1 (at n), obind i2 (at n) with
    | None, None -> []

    | Some (p1, c1, s1), None -> collect1_i `Left  p1 s1 c1 :: doit (n+1)
    | None, Some (p2, c2, s2) -> collect1_i `Right p2 s2 c2 :: doit (n+1)

    | Some (p1, c1, s1), Some (p2, c2, s2) ->
        let sub_p = collect2_s s1 s2 in
        let c =
          match c1, c2 with
          | `B,  c |  c, `B -> c
          | `P, `P | `Q, `Q -> c1
          | `P, `Q | `Q, `P -> `Q
        in
          (p1, p2, c, sub_p) :: doit (n+1)
  in
    doit 0

and collect2_s s1 s2 : ppnode list list =
  match s1, s2 with
  | [], [] -> []

  | i1::s1, [] -> collect2_i (Some i1.i_node) None :: collect2_s s1 []
  | [], i2::s2 -> collect2_i None (Some i2.i_node) :: collect2_s [] s2

  | i1::s1, i2::s2 ->
         collect2_i (Some i1.i_node) (Some i2.i_node)
      :: collect2_s s1 s2

and collect1_i side p s c =
  let (p1, p2), (s1, s2) =
    match side with
    | `Left  -> (p, `None), (s, [])
    | `Right -> (`None, p), ([], s)
  in
    (p1, p2, c, collect2_s s1 s2)

(* -------------------------------------------------------------------- *)
let c_split ?width pp x =
  let buf = Buffer.create 127 in
    begin
      let fmt = Format.formatter_of_buffer buf in
        oiter width (Format.pp_set_margin fmt);
        Format.fprintf fmt "@[<hov 2>%a@]@." pp x
    end;
    Str.split (Str.regexp "\\(\r?\n\\)+") (Buffer.contents buf)

let pp_i_asgn (ppe : PPEnv.t) fmt (lv, e) =
  Format.fprintf fmt "%a =@ %a"
    (pp_lvalue ppe) lv (pp_expr ppe) e

let pp_i_assert (ppe : PPEnv.t) fmt e =
  Format.fprintf fmt "assert (%a)" (pp_expr ppe) e

let pp_i_call (ppe : PPEnv.t) fmt (lv, xp, args) =
  match lv with
  | None ->
      Format.fprintf fmt "%a(%a)"
        (pp_funname ppe) xp
        (pp_list ",@ " (pp_expr ppe)) args

  | Some lv ->
      Format.fprintf fmt "@[<hov 2>%a :=@ %a(%a)@]"
        (pp_lvalue ppe) lv
        (pp_funname ppe) xp
        (pp_list ",@ " (pp_expr ppe)) args

let pp_i_rnd (ppe : PPEnv.t) fmt (lv, e) =
  Format.fprintf fmt "%a =$@ @[<hov 2>%a@]"
    (pp_lvalue ppe) lv (pp_expr ppe) e

let pp_i_if (ppe : PPEnv.t) fmt e =
  Format.fprintf fmt "if (%a) {" (pp_expr ppe) e

let pp_i_else (_ppe : PPEnv.t) fmt _ =
  Format.fprintf fmt "} else {"

let pp_i_while (ppe : PPEnv.t) fmt e =
  Format.fprintf fmt "while (%a) {" (pp_expr ppe) e

let pp_i_blk (_ppe : PPEnv.t) fmt _ =
  Format.fprintf fmt "}"

(* -------------------------------------------------------------------- *)
let c_ppnode1 ~width ppe (pp1 : ppnode1) =
  match pp1 with
  | `Asgn   x -> c_split ~width (pp_i_asgn   ppe) x
  | `Assert x -> c_split ~width (pp_i_assert ppe) x
  | `Call   x -> c_split ~width (pp_i_call   ppe) x
  | `Rnd    x -> c_split ~width (pp_i_rnd    ppe) x
  | `If     x -> c_split ~width (pp_i_if     ppe) x
  | `Else     -> c_split ~width (pp_i_else   ppe) ()
  | `While  x -> c_split ~width (pp_i_while  ppe) x
  | `EBlk     -> c_split ~width (pp_i_blk    ppe) ()
  | `None     -> []

let rec c_ppnode ~width (xl, xr) ppe (pps : ppnode list list) =
  let do1 ((p1, p2, c, subs) : ppnode) : cppnode =
    let p1   = c_ppnode1 ~width (PPEnv.enter ppe xl) p1 in
    let p2   = c_ppnode1 ~width (PPEnv.enter ppe xr) p2 in
    let subs = c_ppnode  ~width (xl, xr) ppe subs in
    let c    = match c with `B -> ' ' | `P -> '.' | `Q -> '?' in
      (p1, p2, c, subs)
  in
    List.map (List.map do1) pps

(* -------------------------------------------------------------------- *)
let rec get_ppnode_stats (pps : cppnode list list) : (int * int) * int list =
  (* Top-level instruction strings (left/right) *)
  let ls = List.map (List.map (fun (l, _, _, _) -> l)) pps
  and rs = List.map (List.map (fun (_, r, _, _) -> r)) pps in

  (* Sub printing commands *)
  let subs = List.map (List.map (fun (_, _, _, pps) -> pps)) pps in
  let subs = List.flatten subs in

  (* Sub stats *)
  let stats = List.split (List.map get_ppnode_stats subs) in

  (* Max line length *)
  let maxl, maxr =
    List.fold_left
      (fun (maxl, maxr) (l1, r1) -> (max maxl l1, max maxr r1))
      (0, 0) (fst stats)
  in

  let maxl, maxr =
    let max1 b lines =
      let for1 m s = max m (String.length s) in
        List.fold_left (List.fold_left (List.fold_left for1)) b lines
    in
      (max1 (2+maxl) ls, max1 (2+maxr) rs)
  in

  (* Maximum length for sub-blocks *)
  let maxsublen =
    match List.length pps, snd stats with
    | 0, []      -> []
    | n, []      -> [n]
    | n, st1::st -> n :: (List.fold_left (List.fusion max) st1 st)

  in
    ((maxl, maxr), maxsublen)

let get_ppnode_stats pps =
  let ndigits n = int_of_float (ceil (log10 (float_of_int (n+1)))) in
  let ((maxl, maxr), mb) = get_ppnode_stats pps in

    ((max maxl 25, max maxr 25), List.map ndigits mb)

(* -------------------------------------------------------------------- *)
let pp_depth mode =
  let rec pp_depth fmt (s, d) =
    match s, d with
    | [], []   -> ()
    | [], _::_ -> assert false

    | s1::s, [] ->
        let sp = match s with [] -> "" | _ -> "-" in
        Format.fprintf fmt "%s%s" (String.make s1 '-') sp;
        Format.fprintf fmt "%a" pp_depth (s, [])

    | s1::s, d1::d -> begin
        let (d1, c1) = ((snd d1) + 1, fst d1) in

        match mode with
        | `Plain -> begin
          let sp = match s with [] -> "" | _ -> "-" in
            match d with
            | [] -> Format.fprintf fmt "%*d%s" s1 d1 sp
            | _  -> Format.fprintf fmt "%*d%c" s1 d1 c1
        end
        | `Blank ->
          let sp = match s with [] -> "" | _ -> " " in
            Format.fprintf fmt "%*s%s" s1 "" sp
      end;
      Format.fprintf fmt "%a" pp_depth (s, d)
  in
    fun stats d fmt -> ignore (pp_depth fmt (stats, List.rev d))

let pp_node_r side ((maxl, maxr), stats) =
  let rec pp_node_r idt depth fmt node =
    let fori offset (node1 : cppnode list) =
      let do1 ((ls, rs, pc, sub) : cppnode) =
        let forline mode l r =
          let l = odfl "" l and r = odfl "" r in
            match side with
            | `Both ->
                Format.fprintf fmt "%-*s (%t) %-*s@\n%!"
                  maxl (Printf.sprintf "%*s%s" (2*idt) "" l)
                  (pp_depth mode stats ((pc, offset) :: depth))
                  maxr (Printf.sprintf "%*s%s" (2*idt) "" r)

            | `Left ->
                Format.fprintf fmt "(%t)  %-*s@\n%!"
                  (pp_depth mode stats ((pc, offset) :: depth))
                  maxl (Printf.sprintf "%*s%s" (2*idt) "" l)
        in
  
        let (l , r ) = (List.ohead ls, List.ohead rs) in
        let (ls, rs) = (List.otail ls, List.otail rs) in
  
          forline `Plain l r;
          List.iter2o(forline `Blank) (odfl [] ls) (odfl [] rs);
          pp_node_r (idt+1) ((pc, offset) :: depth) fmt sub
      in
        List.iter do1 node1
  
    in
      List.iteri fori node
  in
    fun idt depth fmt node -> pp_node_r idt depth fmt node

let pp_node mode fmt node =
  let stats = get_ppnode_stats node in
    pp_node_r mode stats 0 [] fmt node

(* -------------------------------------------------------------------- *)
let pp_pre (ppe : PPEnv.t) fmt pre =
  let pre = c_split (pp_form ppe) pre in
    List.iter
      (fun x -> Format.fprintf fmt "??> %s@\n%!" x)
      pre

(* -------------------------------------------------------------------- *)
let pp_post (ppe : PPEnv.t) fmt post =
  let post = c_split (pp_form ppe) post in
    List.iter
      (fun x -> Format.fprintf fmt "--> %s@\n%!" x)
      post

(* -------------------------------------------------------------------- *)
let pp_hoareF (ppe : PPEnv.t) fmt hf =
  Format.fprintf fmt "%a@\n%!" (pp_pre ppe) hf.hf_pr;
  Format.fprintf fmt "    %a@\n%!" (pp_funname ppe) hf.hf_f;
  Format.fprintf fmt "@\n%a%!" (pp_post ppe) hf.hf_po

(* -------------------------------------------------------------------- *)
let pp_hoareS (ppe : PPEnv.t) fmt hs =
  let ppe =
    { ppe with
        PPEnv.ppe_env = EcEnv.Memory.push hs.hs_m ppe.PPEnv.ppe_env }
  in

  let ppnode = collect2_s hs.hs_s.s_node [] in
  let ppnode =
    c_ppnode ~width:80
      (EcMemory.xpath hs.hs_m, EcMemory.xpath hs.hs_m)
      ppe ppnode
  in
    Format.fprintf fmt "Context : %a@\n%!" (pp_funname ppe) (EcMemory.xpath hs.hs_m);
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a%!" (pp_pre ppe) hs.hs_pr;
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a" (pp_node `Left) ppnode;
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a%!" (pp_post ppe) hs.hs_po

(* -------------------------------------------------------------------- *)
let string_of_hrcmp = function
  | FHle -> "[=]"
  | FHeq -> "[<=]"
  | FHge -> "[>=]"

(* -------------------------------------------------------------------- *)
let pp_bdhoareF (ppe : PPEnv.t) fmt hf =
  let scmp = string_of_hrcmp hf.bhf_cmp in

  Format.fprintf fmt "%a@\n%!" (pp_pre ppe) hf.bhf_pr;
  Format.fprintf fmt "    %a@\n%!" (pp_funname ppe) hf.bhf_f;
  Format.fprintf fmt "    %s @[<hov 2>%a@]@\n%!" scmp (pp_form ppe) hf.bhf_bd;
  Format.fprintf fmt "@\n%a%!" (pp_post ppe) hf.bhf_po

(* -------------------------------------------------------------------- *)
let pp_bdhoareS (ppe : PPEnv.t) fmt hs =
  let ppe =
    { ppe with
        PPEnv.ppe_env = EcEnv.Memory.push hs.bhs_m ppe.PPEnv.ppe_env }
  in

  let ppnode = collect2_s hs.bhs_s.s_node [] in
  let ppnode =
    c_ppnode ~width:80
      (EcMemory.xpath hs.bhs_m, EcMemory.xpath hs.bhs_m)
      ppe ppnode
  in

  let scmp = string_of_hrcmp hs.bhs_cmp in

    Format.fprintf fmt "Context : %a@\n%!" (pp_funname ppe) (EcMemory.xpath hs.bhs_m);
    Format.fprintf fmt "Bound   : @[<hov 2>%s %a@]@\n%!" scmp (pp_form ppe) hs.bhs_bd;
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a%!" (pp_pre ppe) hs.bhs_pr;
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a" (pp_node `Left) ppnode;
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a%!" (pp_post ppe) hs.bhs_po

(* -------------------------------------------------------------------- *)
let pp_equivF (ppe : PPEnv.t) fmt ef =
  Format.fprintf fmt "%a@\n%!" (pp_pre ppe) ef.ef_pr;
  Format.fprintf fmt "    %a ~ %a@\n%!"
    (pp_funname ppe) ef.ef_fl
    (pp_funname ppe) ef.ef_fr;
  Format.fprintf fmt "@\n%a%!" (pp_post ppe) ef.ef_po

(* -------------------------------------------------------------------- *)
let pp_equivS (ppe : PPEnv.t) fmt es =
  let ppe =
    List.fold_left
      (fun ppe m ->
         { ppe with
             PPEnv.ppe_env = EcEnv.Memory.push m ppe.PPEnv.ppe_env })
      ppe [es.es_ml; es.es_mr]
  in

  let ppnode = collect2_s es.es_sl.s_node es.es_sr.s_node in
  let ppnode =
    c_ppnode ~width:40
      (EcMemory.xpath es.es_ml, EcMemory.xpath es.es_mr)
      ppe ppnode
  in
    Format.fprintf fmt "Left  : %a@\n%!" (pp_funname ppe) (EcMemory.xpath es.es_ml);
    Format.fprintf fmt "Right : %a@\n%!" (pp_funname ppe) (EcMemory.xpath es.es_mr);
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a%!" (pp_pre ppe) es.es_pr;
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a" (pp_node `Both) ppnode;
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a%!" (pp_post ppe) es.es_po

(* -------------------------------------------------------------------- *)
let goalline = String.make 72 '-'

let pp_goal (ppe : PPEnv.t) fmt (n, (hyps, concl)) =
  let pp_hyp fmt (id, k) = 
    let dk fmt =
      match k with
      | EcBaseLogic.LD_var (ty, _body) -> pp_type ppe fmt ty
      | EcBaseLogic.LD_mem _           -> Format.fprintf fmt "memory"
      | EcBaseLogic.LD_modty (p, sm)   -> pp_modtype ppe fmt (p, sm)
      | EcBaseLogic.LD_hyp f           -> pp_form ppe fmt f
    in
      Format.fprintf fmt "%-.2s: @[<hov 2>%t@]@\n%!" (EcIdent.name id) dk
  in
    begin
      match n with
      | 0 -> Format.fprintf fmt "Current goal@\n@\n%!"
      | _ -> Format.fprintf fmt "Current goal (remaining: %d)@\n@\n%!" n
    end;

    begin
      match hyps.EcBaseLogic.h_tvar with
      | [] -> Format.fprintf fmt "Type variables: <none>@\n\n%!"
      | tv ->
          Format.fprintf fmt "Type variables: %a@\n\n%!"
            (pp_list ", " (pp_tyvar ppe)) tv
    end;
    List.iter (pp_hyp fmt) (List.rev hyps.EcBaseLogic.h_local);
    Format.fprintf fmt "%s@\n%!" goalline;

    begin
      match concl.f_node with
      | FbdHoareF hf -> pp_bdhoareF ppe fmt hf
      | FbdHoareS hs -> pp_bdhoareS ppe fmt hs
      | FhoareF hf   -> pp_hoareF   ppe fmt hf
      | FhoareS hs   -> pp_hoareS   ppe fmt hs
      | FequivF ef   -> pp_equivF   ppe fmt ef
      | FequivS es   -> pp_equivS   ppe fmt es
      | _ -> Format.fprintf fmt "%a@\n%!" (pp_form ppe) concl
    end

(* -------------------------------------------------------------------- *)
let pp_theory _ _ _ = ()
