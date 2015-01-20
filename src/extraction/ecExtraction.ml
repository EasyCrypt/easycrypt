(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

open EcMaps
open EcUtils
open EcIdent
open EcTheory
open EcDecl
open EcPath
open EcTypes
open EcEnv

let error _s = assert false 

(* Ocaml representation *)
type ocaml_name = 
  { oname_path : string list;       (* full path *)
    mutable oname_base : string; }

type ocaml_ty = 
  | OTvar  of ocaml_name
  | OTtuple of ocaml_ty list
  | OTconstr of ocaml_name * ocaml_ty list
  | OTfun of ocaml_ty * ocaml_ty

type opattern = 
  | Oploc of ocaml_name
  | Optuple of ocaml_name list

type ocaml_expr = 
  | Olam   of (ocaml_name * ocaml_ty) list * ocaml_expr 
  | Oint   of int                         
  | Olocal of ocaml_name
  | Oop    of ocaml_name
  | Oapp   of ocaml_expr * ocaml_expr list
  | Olet   of opattern * ocaml_expr * ocaml_expr
  | Otuple of ocaml_expr list 
  | Oif    of ocaml_expr * ocaml_expr * ocaml_expr
  | Oproj  of (int * int) * ocaml_expr

type ocaml_op_decl = 
  | OOabs of ocaml_ty
  | OOdef of ocaml_expr

type ocaml_op_decl_full = ocaml_name list * ocaml_op_decl

type ocaml_ty_decl = ocaml_name list * ocaml_ty option

type ocaml_decl = {
  odecl_path : path;
  odecl_name : ocaml_name; 
  odecl_kind : ocaml_decl_kind;
}

and ocaml_decl_kind = 
  | ODKty of ocaml_ty_decl
  | ODKop of ocaml_op_decl_full
  | ODKmod of ocaml_mod_decl 

and ocaml_mod_decl = ocaml_decl list

(* ocaml_keyword *)
let ocaml_keyword = 
  List.fold_left (fun s x -> Sstr.add x s) Sstr.empty 
    [ "let"; "rec"; "in";
      "if"; "then"; "else"; "true"; "false";
      "type"; "as";
      "module"; "struct"; "sig"; "begin"; "end"; 
      "match"; "with"; "|"; "->"; "try"; "raise"; "when"; "where"; 
      "unit"; "int"; "bool"; "array"; 
      "()"; "=" ]  

(**********************************************************************)
(* Make names uniques and compatibles with ocaml keyword              *)

let uniq_name restr s =
  let s' = 
    if Sstr.mem s restr then
      let rec aux i = 
        let s' = s^(string_of_int i) in
        if Sstr.mem s' restr then aux (i+1) 
        else s' in
      aux 0
    else s in
  Sstr.add s' restr, s'

let uniq_add_local restr oname =
  let restr, s = uniq_name restr oname.oname_base in
  if not (oname.oname_base == s) then oname.oname_base <- s;
  restr
  
let uniq_add_locals restr onames = 
  List.fold_left uniq_add_local restr onames
 
let uniq_add_binding restr onames = 
  List.fold_left (fun restr (oname,_) -> uniq_add_local restr oname) 
    restr onames

let uniq_add_opat restr = function
  | Oploc s -> uniq_add_local restr s 
  | Optuple ls -> uniq_add_locals restr ls 

let rec uniq_expr restr = function
  | Olam(xs,e) ->
    let restr = uniq_add_binding restr xs in
    uniq_expr restr e
  | Oint _ | Olocal _ | Oop _ -> ()
  | Oapp(e,es) ->
    uniq_expr restr e; List.iter (uniq_expr restr) es
  | Olet(p,e1,e2) ->
    uniq_expr restr e1;
    let restr = uniq_add_opat restr p in
    uniq_expr restr e2
  | Otuple es -> List.iter (uniq_expr restr) es
  | Oproj (_, e) -> uniq_expr restr e
  | Oif(e1,e2,e3) -> 
    uniq_expr restr e1; uniq_expr restr e2; uniq_expr restr e3 

let is_mod odecl = 
  match odecl.odecl_kind with
  | ODKmod _ -> true
  | _ -> false 

let rec uniq_decl restr odecl =
  let restr = 
    if is_mod odecl then restr 
    else uniq_add_local restr odecl.odecl_name in
  uniq_decl_kind restr odecl.odecl_kind;
  restr

and uniq_decl_kind restr odecl_kind =
  match odecl_kind with
  | ODKty (tparams, _) -> 
    ignore (uniq_add_locals restr tparams)
  | ODKop (tparams, opd) ->
    let restr = uniq_add_locals restr tparams in
    begin match opd with
    | OOabs _ -> ()
    | OOdef e -> uniq_expr restr e
    end
  | ODKmod ld -> uniq_mod_decl restr ld

and uniq_mod_decl restr ld = 
  ignore (List.fold_left uniq_decl restr ld)

(**********************************************************************)
(* Prettyprinting, output ocaml representation                        *)

let shorten_name mname name =
  let rec aux l1 l2 = 
    match l1, l2 with
    | s1::l1, s2::l2 when s1 = s2 -> aux l1 l2 
    | _ -> l2 in
  let l = aux mname name.oname_path in
  l, name.oname_base

let out_oname mname fmt name = 
  let l, s = shorten_name mname name in
  let pp_path fmt l = 
    if l <> [] then 
      Format.fprintf fmt "%a." 
        (EcPrinting.pp_list  "." Format.pp_print_string) l in
  Format.fprintf fmt "%a%s" pp_path l s

let pp_paren pp fmt a = 
  Format.fprintf fmt "@[<hov 2>(%a)@]" pp a

let out_tvar fmt oname = 
  assert (oname.oname_path = []);
  Format.fprintf fmt "'%s" oname.oname_base

let rec out_oty mname fmt oty = 
  match oty with
  | OTvar s -> out_tvar fmt s
  | OTtuple tys -> out_tytuple mname fmt tys
  | OTconstr(s,otys) ->
    Format.fprintf fmt "%a%a" (out_tyargs mname) otys (out_oname mname) s
  | OTfun(ot1,ot2) ->
    Format.fprintf fmt "@[<hov 2>%a ->@ %a@]" 
      (out_oty_bf mname) ot1 (out_oty mname) ot2

and out_oty_bf mname fmt oty = 
  match oty with
  | OTfun _ -> pp_paren (out_oty mname) fmt oty
  | _ -> out_oty mname fmt oty

and out_oty_bfp mname fmt oty = 
  match oty with
  | OTfun _ | OTtuple _ -> pp_paren (out_oty mname) fmt oty
  | _ -> out_oty mname fmt oty

and out_tytuple mname fmt tys = 
  match tys with
  | [] -> Format.fprintf fmt "unit"
  | _ -> 
    Format.fprintf fmt "@[<hov 0>%a@]"
      (EcPrinting.pp_list " *@ " (out_oty mname)) tys

and out_tyargs mname fmt tys = 
  match tys with
  | [] -> ()
  | [ty] -> Format.fprintf fmt "%a " (out_oty_bfp mname) ty
  | _ -> pp_paren (EcPrinting.pp_list ",@ " (out_oty mname)) fmt tys

let out_ovar fmt oname = 
  assert (oname.oname_path = []);
  Format.fprintf fmt "%s" oname.oname_base

let out_opat fmt = function
  | Oploc s -> out_ovar fmt s
  | Optuple ls ->
    Format.fprintf fmt "@[<hov 1>(%a)@]" (EcPrinting.pp_list ",@ " out_ovar) ls

let rec out_expr mname fmt e = 
  match e with 
  | Olam(ids,e) ->
    Format.fprintf fmt "@[<hov 2>fun %a ->@ %a@]"
      (EcPrinting.pp_list "@ " (fun fmt (s,_) -> out_ovar fmt s))
      ids (out_expr mname) e
  | Oint n -> Format.fprintf fmt "%i" n
  | Olocal s -> out_ovar fmt s 
  | Oop s -> out_oname mname fmt s
  | Oapp (e,es) -> 
    Format.fprintf fmt "@[<hov 2>%a@]"
      (EcPrinting.pp_list "@ " (out_bexpr mname)) (e::es)
  | Olet(p,e1,e2) ->
    Format.fprintf fmt "@[<hov 0>let %a =@;<1 2>@[%a@]@ in@ %a@]"
      out_opat p (out_expr mname) e1 (out_expr mname) e2
  | Otuple es -> 
    pp_paren (EcPrinting.pp_list ",@ " (out_texpr mname)) fmt es
  | Oif(e1,e2,e3) ->
    Format.fprintf fmt "@[@[<hov 2>(if %a@ then@ %a@]@ @[<hov 2>else@ %a)@]@]"
      (out_expr mname) e1 (out_expr mname) e2 
      (out_expr mname) e3
  | Oproj ((i, n), e) ->
      let var idx = Printf.sprintf "x_%d" idx in
      Format.fprintf fmt "@[<hov 2>(fun (%s) -> %s)@ %a@]"
        (String.concat ", " (List.init n var)) (var i)
        (out_bexpr mname) e

and out_bexpr mname fmt e = 
  match e with
  | Olam _ | Oapp _ | Olet _ | Oif _ | Oproj _ ->
    EcPrinting.pp_paren (out_expr mname) fmt e
  | _ -> out_expr mname fmt e

and out_texpr mname fmt e = 
  match e with
  | Olam _ | Olet _ | Oif _ -> 
    EcPrinting.pp_paren (out_expr mname) fmt e
  | _ -> out_expr mname fmt e

let out_header fmt p = 
  Format.fprintf fmt "(* %a *)@\n"
    (EcPrinting.pp_list "." Format.pp_print_string) 
    (List.tl (EcPath.tolist p))

let out_op_decl mname fmt s od = 
  match od with
  | OOabs ty ->
    Format.fprintf fmt "@[<hov 2>let %s : %a =@\nassert false (* TO FILL *)@]"
      s (out_oty mname) ty
  | OOdef e ->
    let bd,e = 
      match e with 
      | Olam(bd,e) -> bd, e 
      | _ -> [], e in
    Format.fprintf fmt "@[<hov 2>let %s @[<hov 0>%a@] =@\n%a@]" 
      s
      (EcPrinting.pp_list "@ " 
         (fun fmt (s,ty) -> 
           Format.fprintf fmt "(%a : %a)" 
             out_ovar s (out_oty mname) ty)) bd
      (out_expr mname) e

let out_ty_decl mname fmt s (ids, oty) =
  let pp_typarams fmt ids = 
    match ids with
    | [] -> ()
    | [s] -> Format.fprintf fmt "%a " out_tvar s 
    | _ -> 
      Format.fprintf fmt "@[<hov 1>(%a) @]"
        (EcPrinting.pp_list ",@ " out_tvar)
        ids in 
  match oty with
  | None -> 
    Format.fprintf fmt "type %a%s (* TO FILL *)" pp_typarams ids s
  | Some ty ->
    Format.fprintf fmt "@[<hov 2>type %a%s =@ @[%a@]@]" pp_typarams ids 
      s (out_oty mname) ty
  
let rec out_odecl mname fmt odecl = 
  out_header fmt odecl.odecl_path;
  match odecl.odecl_kind with
  | ODKty otyd ->
    out_ty_decl mname fmt odecl.odecl_name.oname_base otyd
  | ODKop(_,opd) ->
    out_op_decl mname fmt odecl.odecl_name.oname_base opd
  | ODKmod modd ->
    out_mod mname fmt odecl.odecl_name.oname_base modd

and out_mod mname fmt s modd =
  let mname = mname @ [s] in
  Format.fprintf fmt "@[<v>module %s = struct@\n@\n  %a@\n@\nend@]"
    s (out_mod_decl mname) modd

and out_mod_decl mname fmt modd = 
  Format.fprintf fmt "@[<v>%a@]"
    (EcPrinting.pp_list "@\n@\n" (out_odecl mname)) modd




(**********************************************************************)
(* compilation easycrypt to ocaml                                     *)


(* compilation environment *) 

type 'def ocaml_def = { 
  odef_name         : ocaml_name;
  odef_def          : 'def option;
       (* None means use the an external function *) 
} 


type extract_env = {
  mp_ty     : ocaml_ty_decl ocaml_def Hp.t;
  mp_op     : ocaml_op_decl_full ocaml_def Hp.t;
}

let eempty () = {
  mp_ty = Hp.create 17;
  mp_op = Hp.create 17;
}

module WI = Why3.Ident

let sanitizer_tvar s =
  assert (String.length s >= 2 && s.[0] = '\'');
  let s = String.sub s 1 (String.length s - 1) in
  let s = WI.sanitizer WI.char_to_lalnumus WI.char_to_alnumus s in
  { oname_path = []; oname_base = s }

let sanitizer_local = 
  fun s -> WI.sanitizer WI.char_to_lalnumus WI.char_to_alnumus s

let mk_odef p s def = 
  let name = { 
    oname_path = EcPath.tolist p; 
    oname_base = sanitizer_local s } in
  { odef_name = name;
    odef_def = Some def }

let compile_typarams typarams = 
  let do1 vtymap (x, tc) =
    if not (Sp.is_empty tc) then
      error "cannot translate constrained type declaration";
    let s = sanitizer_tvar (EcIdent.name x) in
    Mid.add x s vtymap, s in
  List.map_fold do1 Mid.empty typarams 

let destr_path p = 
  EcUtils.oget (EcPath.prefix p), EcPath.basename p

let rec compile_tyd env eenv p = 
  try (Hp.find eenv.mp_ty p).odef_name 
  with Not_found ->
    let pth, s = destr_path p in 
    let tyd = Ty.by_path p env in
    let vtymap, params = compile_typarams tyd.tyd_params in
    let decl = 
      match tyd.tyd_type with
      | `Abstract _  -> None
      | `Datatype _  -> None            (* FIXME: IND HOOK *)
      | `Record   _  -> None            (* FIXME: IND HOOK *)
      | `Concrete ty -> Some (compile_ty env eenv vtymap ty) in
    let res = mk_odef pth s (params,decl) in
    Hp.add eenv.mp_ty p res;
    res.odef_name

and compile_ty env eenv vtymap ty = 
  match ty.ty_node with
  | Tglob _ -> error "cannot extract Tglob"
  | Tunivar _ -> error "cannot extract univar"
  | Tvar id -> 
    let s = try Mid.find id vtymap with Not_found -> assert false in
    OTvar s
  | Ttuple tl -> OTtuple (List.map (compile_ty env eenv vtymap) tl)
  | Tconstr(p,tl) ->
    let on = compile_tyd env eenv p in
    let tl = List.map (compile_ty env eenv vtymap) tl in
    OTconstr(on, tl)
  | Tfun(ty1,ty2) ->
    let ty1 = compile_ty env eenv vtymap ty1 in
    let ty2 = compile_ty env eenv vtymap ty2 in
    OTfun(ty1,ty2)
      
let compile_add_local lmap id = 
  assert (not (Mid.mem id lmap));
  let name = 
    { oname_path = [];
      oname_base = sanitizer_local (EcIdent.name id) } in
  Mid.add id name lmap, name
  
let compile_id lmap id = 
  try Mid.find id lmap with Not_found -> assert false

let rec compile_op env eenv p = 
  try (Hp.find eenv.mp_op p).odef_name 
  with Not_found ->
    let pth, s = destr_path p in 
    let op = Op.by_path p env in
    let vtymap, typarams = compile_typarams op.op_tparams in
    let def = 
      match op.op_kind with
      | OB_oper (Some (OP_Plain body)) ->
        OOdef (compile_expr env eenv vtymap Mid.empty body)
      | OB_oper (Some (OP_Constr _)) ->
        assert false                    (* FIXME: IND HOOK *)
      | OB_oper (Some (OP_Record _)) ->
        assert false                    (* FIXME: IND HOOK *)
      | OB_oper (Some (OP_Proj _)) ->
        assert false                    (* FIXME: IND HOOK *)
      | OB_oper (Some (OP_Fix _)) ->
        assert false                    (* FIXME: IND HOOK *)
      | OB_oper (Some (OP_TC)) ->
        assert false                    (* FIXME: TC HOOK *)
      | OB_oper None ->
        OOabs (compile_ty env eenv vtymap op.op_ty) 
      | OB_pred _ -> error "cannot extract predicate" in
    let res = mk_odef pth s (typarams, def) in
    Hp.add eenv.mp_op p res;
    res.odef_name 

and compile_expr env eenv vtymap lmap e = 
  match e.e_node with
  | Elam(bd,e) ->
    let compile_bd lmap (id,ty) =
      let ty = compile_ty env eenv vtymap ty in
      let lmap, name = compile_add_local lmap id in
      lmap, (name, ty) in
    let lmap, bd = List.map_fold compile_bd lmap bd in
    let body = compile_expr env eenv vtymap lmap e in
    Olam(bd, body) 
  | Eint n -> Oint n
  | Elocal id -> Olocal (compile_id lmap id)
  | Evar _ -> error "cannot extract program variable"
  | Eop(p,_) -> Oop (compile_op env eenv p)
  | Eapp(e,es) -> 
    let e = compile_expr env eenv vtymap lmap e in
    let es = List.map (compile_expr env eenv vtymap lmap) es in
    Oapp(e,es)
  | Elet(p,e1,e2) ->
    let e1 = compile_expr env eenv vtymap lmap e1 in
    let lmap, p = 
      match p with
      | LSymbol (id, _) -> 
        let lmap, name = compile_add_local lmap id in
        lmap, Oploc name
      | LTuple ids ->
        let lmap, names = 
          List.map_fold (fun lmap (id,_) ->
            compile_add_local lmap id) lmap ids in
        lmap, Optuple names
      | LRecord _ -> assert false       (* FIXME: IND HOOK *)
    in
    let e2 = compile_expr env eenv vtymap lmap e2 in
    Olet(p,e1,e2)
  | Etuple es ->
    Otuple (List.map (compile_expr env eenv vtymap lmap) es)
  | Eproj (e, i) -> begin
    match (EcEnv.Ty.hnorm e.e_ty env).ty_node with
    | Ttuple ts ->
      let n = List.length ts in
      let e = compile_expr env eenv vtymap lmap e in
      Oproj ((i, n), e)
    | _ -> assert false
  end
  | Eif(e1,e2,e3) ->
    let e1 = compile_expr env eenv vtymap lmap e1 in
    let e2 = compile_expr env eenv vtymap lmap e2 in
    let e3 = compile_expr env eenv vtymap lmap e3 in
    Oif(e1,e2,e3)

let rec compile_theory env eenv p = 
  match Theory.by_path p env with
  | (cth, `Concrete) ->
      List.iter (compile_thitem env eenv p) cth.cth_struct 
  | _ ->
      ()

and compile_thitem env eenv p = function
  | CTh_type(s,_) -> ignore (compile_tyd env eenv (EcPath.pqname p s))
  | CTh_operator(s,op) ->
      if not (is_pred op) then 
        ignore (compile_op env eenv (EcPath.pqname p s))
  | CTh_theory (s,_) -> compile_theory env eenv (EcPath.pqname p s)
  | CTh_export _ | CTh_modtype _ | CTh_module _ 
  | CTh_axiom _ | CTh_instance _ | CTh_typeclass _ 
  | CTh_baserw _ | CTh_addrw _ -> ()

(*************************************************************************)
(* Once the compilation of every element is done we can extract the      *)
(*   needed representation                                               *)

let rec finalize_items eenv p items =
  let rec aux r items = 
    match items with
    | [] -> List.rev r
    | i::items -> aux (finalize_item eenv p i r) items in
  aux [] items

and finalize_item eenv p item r =
  match item with
  | CTh_type(s,_) -> 
    let ps = EcPath.pqname p s in
    begin match Hp.find_opt eenv.mp_ty ps with
    | Some odef when odef.odef_def <> None ->
      let decl = {
        odecl_path = ps;
        odecl_name = odef.odef_name;
        odecl_kind = ODKty (oget odef.odef_def);
      } in
      decl :: r
    | _ -> r
    end
  | CTh_operator(s,op) ->
    if is_pred op then r 
    else 
      let ps = EcPath.pqname p s in
      begin match Hp.find_opt eenv.mp_op ps with
      | Some odef when odef.odef_def <> None ->
        let decl = {
          odecl_path = ps;
          odecl_name = odef.odef_name;
          odecl_kind = ODKop (oget odef.odef_def);
        } in
        decl :: r
      | _ -> r
      end
  | CTh_theory (s,(cth,`Concrete)) -> 
    let ps = EcPath.pqname p s in
    let items = finalize_items eenv ps cth.cth_struct in
    if items = [] then r
    else 
      let decl = { 
        odecl_path = ps;
        odecl_name = { oname_path = EcPath.tolist p; oname_base = s };
        odecl_kind = ODKmod items; } in
      decl :: r
  | CTh_theory (_,(_,`Abstract))
  | CTh_export _ | CTh_modtype _ | CTh_module _ 
  | CTh_axiom _ | CTh_instance _ | CTh_typeclass _ 
  | CTh_baserw _ |CTh_addrw _ -> r
  
let finalize required env eenv =
  let ct = (EcEnv.ctheory_of_ctheory_w3 (EcEnv.Theory.close env)).cth_struct in
  assert (
    match List.hd ct with
    | CTh_theory(s, _) -> s = EcCoreLib.i_Pervasive
    | _ -> false);
  let required = EcCoreLib.i_Pervasive :: List.rev required  in
  let required = 
    List.map 
      (fun id -> 
        let cth = EcEnv.Theory.by_path (EcPath.pqname EcCoreLib.p_top id) env in
        CTh_theory (id, cth)) 
      required in
  let ct = required @ List.tl ct in
  finalize_items eenv EcCoreLib.p_top ct 

open EcParsetree

let oname_of_rlist ls = 
  { oname_path = List.rev (List.tl ls);
    oname_base = List.hd ls } 

let rec compile_dummy_th p ls cth =
  let modd = compile_dummy_items p ls cth.cth_struct in
  { odecl_path = p;
    odecl_name = oname_of_rlist ls;
    odecl_kind = ODKmod modd }

and compile_dummy_items p ls items =
  let rec aux r items = 
    match items with
    | [] -> List.rev r 
    | i::items -> aux (compile_dummy_item p ls r i) items in
  aux [] items 

and compile_dummy_item p ls r item = 
  match item with
  | CTh_type(s,_) -> 
    let name = oname_of_rlist (sanitizer_local s :: ls) in
    { odecl_path = EcPath.pqname p s;
      odecl_name = name;
      odecl_kind = ODKty ([], None) } :: r
  | CTh_operator(s,op) ->
    if is_pred op then r 
    else 
      let name = oname_of_rlist (sanitizer_local s :: ls) in
      { odecl_path = EcPath.pqname p s;
        odecl_name = name;
        odecl_kind = ODKop ([], OOdef (Oint 0));
      } :: r
  | CTh_theory (s,(cth,`Concrete)) ->
    compile_dummy_th (EcPath.pqname p s) (s::ls) cth :: r
  | CTh_theory (_,(_,`Abstract))
  | CTh_export _ | CTh_modtype _ | CTh_module _ 
  | CTh_axiom _ | CTh_instance _ | CTh_typeclass _ 
  | CTh_baserw _|CTh_addrw _ -> r
  

let rec add_dummy_decl eenv decl = 
  match decl.odecl_kind with
  | ODKty _ -> 
    Hp.add eenv.mp_ty decl.odecl_path 
      { odef_name = decl.odecl_name; odef_def = None }
  | ODKop _ ->
    Hp.add eenv.mp_op decl.odecl_path
      { odef_name = decl.odecl_name; odef_def = None }
  | ODKmod modd ->
    List.iter (add_dummy_decl eenv) modd

 
let rec add_withs check env eenv withextract = 
  List.iter (add_with check env eenv) withextract 

and add_with check env eenv (toex, s) = 
  let oname = List.rev (Str.split (Str.regexp "\\.") s) in
  match toex with
  | ExOp qs -> add_withop check env eenv qs oname 
  | ExTy qs -> add_withty check env eenv qs oname
  | ExTh qs -> add_withth check env eenv qs oname

and add_withop check env eenv qs oname =
  try 
    add_withop_p eenv (Op.lookup_path (EcLocation.unloc qs) env) oname
  with LookupFailure _ when not check -> ()
    
and add_withop_p eenv p oname =
  let oname = oname_of_rlist oname in
  Hp.add eenv.mp_op p { odef_name = oname; odef_def = None; }

and add_withty check env eenv qs oname = 
  try 
    add_withty_p eenv (Ty.lookup_path (EcLocation.unloc qs) env) oname 
  with LookupFailure _ when not check -> ()

and add_withty_p eenv p oname =
  let oname = oname_of_rlist oname in
  Hp.add eenv.mp_ty p { odef_name = oname; odef_def = None }

and add_withth check env eenv qs oname = 
  try 
    let (p,(cth,_)) = Theory.lookup (EcLocation.unloc qs) env in
    let decl = compile_dummy_th p oname cth in
    ignore (uniq_decl ocaml_keyword decl);
    add_dummy_decl eenv decl
  with LookupFailure _ when not check -> ()

let init_withextract =
  let dummy x = EcLocation.mk_loc EcLocation._dummy x in
  let perv x = dummy ([EcCoreLib.i_top; EcCoreLib.i_Pervasive], x) in
  let operv x = "Pervasives." ^ x in
  let tint x = dummy ([EcCoreLib.i_top; "Int"], x) in
  [
    (* Pervasive *)
    ExTh (dummy ([EcCoreLib.i_top], EcCoreLib.i_Pervasive)), "EcPervasive"; 
    ExTy (perv "unit") , "unit"       ;
    ExTy (perv "bool") , "bool"       ; 
    ExOp (perv "true") , "true"       ;
    ExOp (perv "false"), "false"      ;
    ExTy (perv "int")  , "int"        ;
    ExOp (perv "<=>")  , operv "(==)" ;
    ExOp (perv "||")   , operv "(||)" ;
    ExOp (perv "\\/")  , operv "(||)" ;
    ExOp (perv "&&")   , operv "(&&)" ;
    ExOp (perv "/\\")  , operv "(&&)" ;
    ExOp (perv "[!]")  , operv "not"  ;
    ExOp (perv "=")    , operv "(=)"  ;
    ExOp (perv "tt")   ,       "()"   ;
    (* Int *) 
    (* TODO : this is dangerous : we should use big_int *)
    ExTh (dummy ([EcCoreLib.i_top], "Int")), "EcInt";
    ExOp (tint "[-]")  , operv "(~-)" ;
    ExOp (tint "-")    , operv "(-)"  ;
    ExOp (tint "+")    , operv "(+)"  ;
    ExOp (tint "*")    , operv "( * )";
    ExOp (tint "<=")   , operv "(<=)" ;
    ExOp (tint "<")    , operv "(<)"  ;
    ExOp (tint ">=")   , operv "(>=)" ;
    ExOp (tint ">")    , operv "(>)"  ;
    ExOp (tint "one")  , "1"          ;
    ExOp (tint "zero") , "0"          ;
    ExOp (dummy ([EcCoreLib.i_top; "Int"; "EuclDiv"], "%%")) , operv "(mod)"  ;
    ExOp (dummy ([EcCoreLib.i_top; "Int"; "EuclDiv"], "/%")) , operv "(/)"    ;
    ExOp (dummy ([EcCoreLib.i_top; "Int"; "Extrema"], "max")), operv "max";
    ExOp (dummy ([EcCoreLib.i_top; "Int"; "Extrema"], "min")), operv "min";
    ExOp (dummy ([EcCoreLib.i_top; "Int"; "Abs"], "`|_|"))   , operv "abs";
    (* Bool *)
    ExTh (dummy ([EcCoreLib.i_top], "Bool")), "EcBool";
    (* Pair *)
    ExTh (dummy ([EcCoreLib.i_top], "Pair")), "EcPair";
    ExOp (dummy ([EcCoreLib.i_top; "Pair"], "fst")), operv "fst";
    ExOp (dummy ([EcCoreLib.i_top; "Pair"], "snd")), operv "snd"; 
   ] 

let compile_kind env eenv = function
  | ExOp qs -> 
    let p = Op.lookup_path (EcLocation.unloc qs) env in
    ignore (compile_op env eenv p)
  | ExTy qs ->
    let p = Ty.lookup_path (EcLocation.unloc qs) env in
    ignore (compile_tyd env eenv p)
  | ExTh qs ->
    let p = Theory.lookup_path (EcLocation.unloc qs) env in
    compile_theory env eenv p 
  
let process_extraction env required (file, toextract, withextract) = 
  let eenv = eempty () in
  add_withs false env eenv init_withextract;
  add_withs true env eenv withextract; 
  List.iter (compile_kind env eenv) toextract;
  let modd = finalize required env eenv in
  uniq_mod_decl ocaml_keyword modd;
  let fmt, close = 
    match file with
    | None ->
      let fmt = Format.std_formatter in
      fmt, fun _ -> Format.fprintf fmt "@\n@."
    | Some filename ->
      let module E = struct exception InvalidPath end in

      let rec makedirs filename =
        let dirname = Filename.dirname filename in

        if Sys.file_exists dirname then begin
          if not (Sys.is_directory dirname) then
            raise E.InvalidPath
        end else begin
          makedirs dirname;
          Unix.mkdir filename 0o755
        end
      in

      makedirs (Filename.dirname filename);
      let outc = open_out filename in
      Format.formatter_of_out_channel outc, fun _ -> close_out outc in
  let err = ref None in
  begin 
    try out_mod_decl [EcCoreLib.i_top] fmt modd
    with e -> err := Some e 
  end;
  close (); 
  EcUtils.oiter (fun e -> raise e) !err
 
 
