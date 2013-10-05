open EcTheory
open EcDecl
open EcPath
open EcTypes
open EcEnv

let error _s = assert false 

(* Ocaml representation *)
type ocaml_name = string list 
type ocaml_name_path = ocaml_name * path 

type ocaml_ty = 
  | OTvar  of string
  | OTtuple of ocaml_ty list
  | OTconstr of ocaml_name_path * ocaml_ty list
  | OTfun of ocaml_ty * ocaml_ty

type opattern = 
  | Oploc of string
  | Optuple of string list

type ocaml_expr = 
  | Olam   of (string * ocaml_ty) list * ocaml_expr 
  | Oint   of int                         
  | Olocal of string 
  | Oop    of ocaml_name_path
  | Oapp   of ocaml_expr * ocaml_expr list
  | Olet   of opattern * ocaml_expr * ocaml_expr
  | Otuple of ocaml_expr list 
  | Oif    of ocaml_expr * ocaml_expr * ocaml_expr

type ocaml_op_decl = 
  | OOabs of ocaml_ty
  | OOdef of ocaml_expr

type ocaml_ty_decl = string list * ocaml_ty option

type ocaml_decl_kind = 
  | OCty 
  | OClet
  | OCmod

type ocaml_decl = path * ocaml_decl_kind

type ocaml_mod = 
  { mod_path : path;
    mutable mod_decl  : ocaml_decl list;
    mutable mod_decl2 : ocaml_decl list;
  }

type 'def ocaml_def = { 
  odef_name         : ocaml_name;
  odef_def          : (string * 'def) option;
  mutable odef_done : bool 
} 

(* compilation environment *) 
type extract_env = {
  mp_ty     : ocaml_ty_decl ocaml_def Hp.t;
  mp_op     : ocaml_op_decl ocaml_def Hp.t;
  mp_th     : ocaml_mod     ocaml_def Hp.t;
}

let eempty _ = {
  mp_ty = Hp.create 17;
  mp_op = Hp.create 17;
  mp_th = Hp.create 17;
}

(* Output ocaml representation *)

let pp_paren pp fmt a = 
  Format.fprintf fmt "@[<hov 2>(%a)@]" pp a

let out_name fmt (ls,_) = 
  EcPrinting.pp_list "." Format.pp_print_string fmt ls

let rec out_oty fmt oty = 
  match oty with
  | OTvar s -> Format.fprintf fmt "%s" s
  | OTtuple tys -> out_tytuple fmt tys
  | OTconstr(s,otys) ->
    Format.fprintf fmt "%a%a" out_tyargs otys out_name s
  | OTfun(ot1,ot2) ->
    Format.fprintf fmt "@[<hov 2>%a ->@ %a@]" out_oty_bf ot1 out_oty ot2

and out_oty_bf fmt oty = 
  match oty with
  | OTfun _ -> pp_paren out_oty fmt oty
  | _ -> out_oty fmt oty

and out_oty_bfp fmt oty = 
  match oty with
  | OTfun _ | OTtuple _ -> pp_paren out_oty fmt oty
  | _ -> out_oty fmt oty

and out_tytuple fmt tys = 
  match tys with
  | [] -> Format.fprintf fmt "unit"
  | _ -> 
    Format.fprintf fmt "@[<hov 0>%a@]"
      (EcPrinting.pp_list " *@ " out_oty) tys

and out_tyargs fmt tys = 
  match tys with
  | [] -> ()
  | [ty] -> Format.fprintf fmt "%a " out_oty_bfp ty
  | _ -> pp_paren (EcPrinting.pp_list ",@ " out_oty) fmt tys

let out_opat fmt = function
  | Oploc s -> Format.fprintf fmt "%s" s
  | Optuple ls ->
    Format.fprintf fmt "@[<hov 1>(%a)@]"
      (EcPrinting.pp_list ",@ " (fun fmt s -> Format.fprintf fmt "%s" s)) ls

let rec out_expr fmt e = 
  match e with 
  | Olam(ids,e) ->
    Format.fprintf fmt "@[<hov 2>fun %a ->@ %a@]"
      (EcPrinting.pp_list "@ " (fun fmt (s,_) -> Format.fprintf fmt "%s" s))
      ids out_expr e
  | Oint n -> Format.fprintf fmt "%i" n
  | Olocal s -> Format.fprintf fmt "%s" s
  | Oop s -> out_name fmt s
  | Oapp (e,es) -> 
    Format.fprintf fmt "@[<hov 2>%a@]"
      (EcPrinting.pp_list "@ " out_bexpr) (e::es)
  | Olet(p,e1,e2) ->
    Format.fprintf fmt "@[<hov 0>let %a =@;<1 2>@[%a@]@ in@ %a@]"
      out_opat p out_expr e1 out_expr e2
  | Otuple es -> 
    pp_paren (EcPrinting.pp_list ",@ " out_texpr) fmt es
  | Oif(e1,e2,e3) ->
    Format.fprintf fmt "@[@[<hov 2>(if %a@ then@ %a@]@ @[<hov 2>else@ %a)@]@]"
      out_expr e1 out_expr e2 out_expr e3

and out_bexpr fmt e = 
  match e with
  | Olam _ | Oapp _ | Olet _ | Oif _ ->
    EcPrinting.pp_paren out_expr fmt e
  | _ -> out_expr fmt e

and out_texpr fmt e = 
  match e with
  | Olam _ | Olet _ | Oif _ -> 
    EcPrinting.pp_paren out_expr fmt e
  | _ -> out_expr fmt e

let out_header fmt p = 
  Format.fprintf fmt "(* %a *)@\n"
    (EcPrinting.pp_list "." Format.pp_print_string) 
    (List.tl (EcPath.tolist p))

let out_op_decl fmt p s od = 
  out_header fmt p;
  match od with
  | OOabs ty ->
    Format.fprintf fmt "@[<hov 2>let %s : %a =@\nassert false (* TO FILL *)@]"
      s out_oty ty
  | OOdef e ->
    let bd,e = 
      match e with 
      | Olam(bd,e) -> bd, e 
      | _ -> [], e in
    Format.fprintf fmt "@[<hov 2>let %s @[<hov 0>%a@] =@\n%a@]" 
      s
      (EcPrinting.pp_list "@ " 
         (fun fmt (s,ty) -> Format.fprintf fmt "(%s : %a)" s out_oty ty)) bd
      out_expr e

let out_ty_decl fmt p s ids oty =
  out_header fmt p;
  let pp_typarams fmt ids = 
    match ids with
    | [] -> ()
    | [s] -> Format.fprintf fmt "%s " s
    | _ -> 
      Format.fprintf fmt "@[<hov 1>(%a) @]"
        (EcPrinting.pp_list ",@ " Format.pp_print_string)
        ids in 
  match oty with
  | None -> 
    Format.fprintf fmt "type %a%s (* TO FILL *)" pp_typarams ids s
  | Some ty ->
    Format.fprintf fmt "@[<hov 2>type %a%s =@ @[%a@]@]" pp_typarams ids 
      s out_oty ty
  
let find_odef tbl p = 
  try Hp.find tbl p with Not_found -> assert false 

let find_def tbl p =
  let odef = find_odef tbl p in
  assert odef.odef_done;
  odef.odef_def

let rec out_decl eenv fmt (p, k) =
 
  match k with 
  | OCty ->
    begin match find_def eenv.mp_ty p with
    | None -> ()
    | Some (s,(ids,tyd)) -> out_ty_decl fmt p s ids tyd 
    end
  | OClet -> 
    begin match find_def eenv.mp_op p with
    | None -> ()
    | Some (s,opd) -> out_op_decl fmt p s opd
    end
  | OCmod -> 
    begin match find_def eenv.mp_th p with
    | None -> ()
    | Some (s,mo) ->
      out_header fmt p;
      Format.fprintf fmt "@[module %s = struct@\n  %a@\n@\nend@]"
        s (out_mod eenv) mo.mod_decl2
    end

and out_mod eenv fmt decls = 
  Format.fprintf fmt "@[%a@]"
    (EcPrinting.pp_list "@\n@\n" (out_decl eenv)) (List.rev decls)  
  
(* Compiler *) 

let sanitizer = 
  let char_to c = 
    if c = '*' then "aas" else Why3.Ident.char_to_alnumus c in
  fun s ->
    if s = "false" then "_false"
    else if s = "true" then "_true"
    else Why3.Ident.sanitizer char_to char_to s

let dot_name mo s =
  mo.odef_name@[s]

let eq_string s1 s2 = 
  s1 == s2 || s1 = s2

let rec chop_name ls' ls = 
  match ls', ls with
  | _, [] -> assert false 
  | [], ls -> ls
  | s1::ls', s2::ls2 ->
    if eq_string s1 s2 then chop_name ls' ls2
    else ls

let destr_path p = 
  EcUtils.oget (EcPath.prefix p), sanitizer (EcPath.basename p)

let mk_odef mo s def = 
  { odef_name = dot_name mo s; odef_def = Some(s,def); odef_done = false }

let rec compile_mod eenv p = 
  try Hp.find eenv.mp_th p
  with Not_found ->
    let pp = 
      match EcPath.prefix p with
      | None -> assert false 
      | Some pp -> pp in
    let mo = compile_mod eenv pp in
    let s = EcPath.basename p in
    let res = mk_odef mo s {
      mod_path = p; 
      mod_decl = []; mod_decl2 = [] } in
    let modd = snd (EcUtils.oget mo.odef_def) in
    modd.mod_decl <- (p, OCmod) :: modd.mod_decl;
    Hp.add eenv.mp_th p res;
    res
  
let rec compile_tyd env eenv cname p = 
  let res = 
    try (Hp.find eenv.mp_ty p).odef_name 
    with Not_found ->
      let pth, s = destr_path p in 
      let cname = EcPath.tolist pth in
      let tyd = Ty.by_path p env in
      let decl = 
        match tyd.tyd_type with
        | None -> None
        | Some ty -> Some (compile_ty env eenv cname ty) in
      let params = List.map EcIdent.name tyd.tyd_params in
      let mo = compile_mod eenv pth in
      let res = mk_odef mo s (params,decl) in
      let modd = snd (EcUtils.oget mo.odef_def) in
      modd.mod_decl <- (p, OCty):: modd.mod_decl;
      Hp.add eenv.mp_ty p res;
      res.odef_name in
  chop_name cname res 

and compile_ty env eenv cname ty = 
  match ty.ty_node with
  | Tglob _ -> error "can not extract Tglob"
  | Tunivar _ -> error "can not extract univar"
  | Tvar id -> OTvar (EcIdent.name id)
  | Ttuple tl -> OTtuple (List.map (compile_ty env eenv cname) tl)
  | Tconstr(p,tl) ->
    let on = compile_tyd env eenv cname p in
    let tl = List.map (compile_ty env eenv cname) tl in
    OTconstr((on,p), tl)
  | Tfun(ty1,ty2) ->
    let ty1 = compile_ty env eenv cname ty1 in
    let ty2 = compile_ty env eenv cname ty2 in
    OTfun(ty1,ty2)

      
let rec compile_op env eenv cname p = 
  let res = 
    try (Hp.find eenv.mp_op p).odef_name 
    with Not_found ->
      let pth, s = destr_path p in 
      let op = Op.by_path p env in
      let cname = EcPath.tolist pth in
      let def = 
        match op.op_kind with
        | OB_oper (Some body) ->
          OOdef (compile_expr env eenv cname body)
        | OB_oper None ->
          OOabs (compile_ty env eenv cname op.op_ty) 
        | OB_pred _ -> error "can not extract predicate" in
      let mo = compile_mod eenv pth in
      let res = mk_odef mo s def in
      let modd = snd (EcUtils.oget mo.odef_def) in
      modd.mod_decl <- (p, OClet) :: modd.mod_decl;
      Hp.add eenv.mp_op p res;
      res.odef_name in
  chop_name cname res 
      
and compile_expr env eenv cname e = 
  match e.e_node with
  | Elam(bd,e) ->
    let compile_bd (id,ty) =
      let ty = compile_ty env eenv cname ty in
      EcIdent.name id, ty in
    let bd = List.map compile_bd bd in
    let body = compile_expr env eenv cname e in
    Olam(bd, body) 
  | Eint n -> Oint n
  | Elocal id -> Olocal (EcIdent.name id)
  | Evar _ -> error "can not extract program variable"
  | Eop(p,_) -> Oop (compile_op env eenv cname p,p)
  | Eapp(e,es) -> 
    let e = compile_expr env eenv cname e in
    let es = List.map (compile_expr env eenv cname) es in
    Oapp(e,es)
  | Elet(p,e1,e2) ->
    let p = 
      match p with
      | LSymbol (id, _) -> Oploc (EcIdent.name id)
      | LTuple ids -> Optuple (List.map (fun (id, _) -> EcIdent.name id) ids) in
    let e1 = compile_expr env eenv cname e1 in
    let e2 = compile_expr env eenv cname e2 in
    Olet(p,e1,e2)
  | Etuple es ->
    Otuple (List.map (compile_expr env eenv cname) es)
  | Eif(e1,e2,e3) ->
    let e1 = compile_expr env eenv cname e1 in
    let e2 = compile_expr env eenv cname e2 in
    let e3 = compile_expr env eenv cname e3 in
    Oif(e1,e2,e3)

let rec compile_theory env eenv p = 
  let cth = Theory.by_path p env in
  List.iter (compile_thitem env eenv p) cth.cth_struct 

and compile_thitem env eenv p = function
  | CTh_type(s,_) -> ignore (compile_tyd env eenv [] (EcPath.pqname p s))
  | CTh_operator(s,op) -> 
    if not (is_pred op) then 
      ignore (compile_op env eenv [] (EcPath.pqname p s))
  | CTh_theory (s,_) -> compile_theory env eenv (EcPath.pqname p s)
  | CTh_export _ | CTh_modtype _ | CTh_module _ 
  | CTh_axiom _ | CTh_instance _ -> ()


open EcParsetree

let compile_kind env eenv = function
  | ExOp qs -> 
    let p = Op.lookup_path (EcLocation.unloc qs) env in
    ignore (compile_op env eenv [] p)
  | ExTy qs ->
    let p = Ty.lookup_path (EcLocation.unloc qs) env in
    ignore (compile_tyd env eenv [] p)
  | ExTh qs ->
    let p = Theory.lookup_path (EcLocation.unloc qs) env in
    compile_theory env eenv p 

let rec sort_modp eenv p = 
  let odef = find_odef eenv.mp_th p in
  if not odef.odef_done then begin
    odef.odef_done <- true;
    let _, def = EcUtils.oget odef.odef_def in
    List.iter (sort_decl eenv) def.mod_decl;
    upd_parent eenv p OCmod
  end

and upd_parent eenv p k = 
  let pp = EcUtils.oget (EcPath.prefix p) in
  let ppdef = find_odef eenv.mp_th pp in
  let modu = snd (EcUtils.oget ppdef.odef_def) in
  modu.mod_decl2 <- (p,k) :: modu.mod_decl2;
  sort_modp eenv pp

and sort_decl eenv (p,k) =
  match k with 
  | OCty -> sort_typ eenv p 
  | OClet -> sort_opp eenv p
  | OCmod -> sort_modp eenv p

and sort_typ eenv p = 
  let odef = find_odef eenv.mp_ty p in
  if not odef.odef_done then begin 
    odef.odef_done <- true;
    let (_n,(_p,def)) = EcUtils.oget odef.odef_def in
    EcUtils.oiter (sort_ty eenv) def;
    upd_parent eenv p OCty
  end

and sort_opp eenv p = 
  let odef = find_odef eenv.mp_op p in
  if not odef.odef_done then begin
    odef.odef_done <- true;
    let (_,def) = EcUtils.oget odef.odef_def in
    sort_op eenv def;
    upd_parent eenv p OClet 
  end

and sort_op eenv = function
  | OOabs ty -> sort_ty eenv ty
  | OOdef e  -> sort_expr eenv e

and sort_ty eenv = function
  | OTvar _ -> ()
  | OTtuple tys -> List.iter (sort_ty eenv) tys
  | OTconstr ((_,p),tys) ->
    sort_typ eenv p; List.iter (sort_ty eenv) tys
  | OTfun(ty1,ty2) ->
    sort_ty eenv ty1; sort_ty eenv ty2

and sort_expr eenv = function
  | Olam (bd,e) ->
    List.iter (fun (_,ty) -> sort_ty eenv ty) bd;
    sort_expr eenv e 
  | Oint _ | Olocal _ -> ()
  | Oop (_,p) -> sort_opp eenv p
  | Oapp(e,es) -> List.iter (sort_expr eenv) (e::es)
  | Olet(_,e1,e2) -> sort_expr eenv e1; sort_expr eenv e2
  | Otuple es -> List.iter (sort_expr eenv) es 
  | Oif(e1,e2,e3) -> sort_expr eenv e1; sort_expr eenv e2; sort_expr eenv e3


  

let rec add_withs check env eenv withextract = 
  List.iter (add_with check env eenv) withextract 

and add_with check env eenv (toex, s) = 
  let oname = Str.split (Str.regexp "\ .") s in
  match toex with
  | ExOp qs -> add_withop check env eenv qs oname 
  | ExTy qs -> add_withty check env eenv qs oname
  | ExTh qs -> add_withth check env eenv qs oname

and add_withop check env eenv qs oname =
  try 
    add_withop_p eenv (Op.lookup_path (EcLocation.unloc qs) env) oname
  with LookupFailure _ when not check -> ()
    
and add_withop_p eenv p oname =
  Hp.add eenv.mp_op p 
    { odef_name = oname; odef_def = None; odef_done = true }

and add_withty check env eenv qs oname = 
  try 
    add_withty_p eenv (Ty.lookup_path (EcLocation.unloc qs) env) oname 
  with LookupFailure _ when not check -> ()

and add_withty_p eenv p oname =
  Hp.add eenv.mp_ty p 
    { odef_name = oname; odef_def = None; odef_done = true }

and add_withth check env eenv qs oname = 
  try 
    let (p,cth) = Theory.lookup (EcLocation.unloc qs) env  in
    List.iter (add_citem eenv p (List.rev oname)) cth.cth_struct 
  with LookupFailure _ when not check -> ()

and add_citem eenv p oname = function 
  | CTh_type(s,_) ->
    add_withty_p eenv (EcPath.pqname p s) (List.rev_append oname [sanitizer s])
  | CTh_operator(s,_) ->
    add_withop_p eenv (EcPath.pqname p s) (List.rev_append oname [sanitizer s])
  | CTh_theory(s,cth) ->
    List.iter (add_citem eenv (EcPath.pqname p s) (s::oname)) cth.cth_struct
  | CTh_axiom _ | CTh_modtype _ | CTh_module _
  | CTh_export _ | CTh_instance _ -> ()

let init_withextract =
  let dummy x = EcLocation.mk_loc EcLocation._dummy x in
  let perv x = dummy ([EcCoreLib.id_top; EcCoreLib.id_Pervasive], x) in
  let operv x = "Pervasives." ^ x in
  let tint x = dummy ([EcCoreLib.id_top; "Int"], x) in
  [
   (* Pervasive *)
    ExTh (dummy ([EcCoreLib.id_top], EcCoreLib.id_Pervasive)), "EcPervasive";
    ExOp (perv "true") , "true"       ;
    ExOp (perv "false"), "false"      ;
    ExOp (perv "<=>")  , operv "(==)" ;
    ExOp (perv "||")   , operv "(||)" ;
    ExOp (perv "\\/")  , operv "(||)" ;
    ExOp (perv "&&")   , operv "(&&)" ;
    ExOp (perv "/\\")  , operv "(&&)" ;
    ExOp (perv "[!]")  , operv "not"  ;
    ExOp (perv "=")    , operv "(=)"  ;
    ExOp (perv "tt")   , operv "()"   ;
   (* Int *) 
   (* TODO : this is dangerous : we should use big_int *)
    ExTh (dummy ([EcCoreLib.id_top], "Int")), "EcInt";
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
    ExOp (dummy ([EcCoreLib.id_top; "Int"; "EuclDiv"], "%%")) , operv "(mod)"  ;
    ExOp (dummy ([EcCoreLib.id_top; "Int"; "EuclDiv"], "/%")) , operv "(/)"    ;
    ExOp (dummy ([EcCoreLib.id_top; "Int"; "Extrema"], "max")), operv "max";
    ExOp (dummy ([EcCoreLib.id_top; "Int"; "Extrema"], "min")), operv "min";
    ExOp (dummy ([EcCoreLib.id_top; "Int"; "Abs"], "`|_|"))   , operv "abs";
   (* Bool *)
    ExTh (dummy ([EcCoreLib.id_top], "Bool")), "EcBool";
   (* Pair *)
    ExTh (dummy ([EcCoreLib.id_top], "Pair")), "EcPair";
    ExOp (dummy ([EcCoreLib.id_top; "Pair"], "fst")), operv "fst";
    ExOp (dummy ([EcCoreLib.id_top; "Pair"], "snd")), operv "snd";
   ] 

let process_extraction env (file, toextract, withextract) = 
  let eenv = eempty () in
  let top = EcCoreLib.p_top in
  let topmod = { mod_path = top; mod_decl = []; mod_decl2 = [] } in
  let topdef = { odef_name = [EcPath.basename top];
                 odef_def  = Some (EcCoreLib.id_top, topmod);
                 odef_done = false } in
  Hp.add eenv.mp_th top topdef;
  add_withs false env eenv init_withextract;
  add_withs true env eenv withextract;
  List.iter (compile_kind env eenv) toextract;
  topdef.odef_done <- true;
  List.iter (sort_decl eenv) topmod.mod_decl;
  let fmt, close = 
    match file with
    | None ->
      let fmt = Format.std_formatter in
      fmt, fun _ -> Format.fprintf fmt "@\n@."
    | Some filename ->
      let outc = open_out filename in
      Format.formatter_of_out_channel outc, fun _ -> close_out outc in
  let err = ref None in
  begin try out_mod eenv fmt topmod.mod_decl2; with e -> err := Some e end;
  close (); 
  EcUtils.oiter (fun e -> raise e) !err


  
  
  
  
