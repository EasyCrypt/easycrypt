open EcUtils
open EcMaps
open EcIdent
open EcPath
open EcTypes
open EcDecl
open EcFol
open EcEnv
open EcCoreLib
open EcBaseLogic
open EcWhy3Conv

module P  = EcProvers
module ER = EcReduction
module BI = EcBigInt
module EI = EcInductive

module WIdent  = Why3.Ident
module WTerm   = Why3.Term
module WTy     = Why3.Ty
module WTheory = Why3.Theory
module WDecl   = Why3.Decl
module WTask   = Why3.Task

let w_t_let vs w1 w2 =
  WTerm.t_let_simp w1 (WTerm.t_close_bound vs w2)

let w_t_lets vs ws w2 =
  List.fold_right2 w_t_let vs ws w2

(* -------------------------------------------------------------------- *)
type w3_known_op = WTerm.lsymbol * WTheory.theory
type w3_known_ty = WTy.tysymbol * WTheory.theory

type w3ty = WTy.tysymbol

type w3op_ho =
  [ `HO_DONE of WTerm.lsymbol
  | `HO_TODO of string * WTy.ty list * WTy.ty option
  | `HO_FIX  of WTerm.lsymbol * WDecl.decl * WDecl.decl * bool ref ]

type w3op = {
  (*---*) w3op_fo : w3op_fo;
  (*---*) w3op_ta : WTy.ty list ->
    WTy.ty list * WTy.ty option list * WTy.ty option;
  (* The first list correspond to the type variables
     that do not occur in the type of the operator.
     The translation will automatically add arguments
  *)
  mutable w3op_ho : w3op_ho;
}

and w3op_fo = [
  | `Internal of WTerm.term list -> WTy.ty option -> WTerm.term
  | `LDecl    of WTerm.lsymbol
]

type w3absmod = {
  w3am_ty : WTy.ty;
}

(* -------------------------------------------------------------------- *)

type kpattern =
  | KHole
  | KApp  of EcPath.path * kpattern list
  | KProj of kpattern * int

(* -------------------------------------------------------------------- *)
type tenv = {
  (*---*) te_env        : EcEnv.env;
  mutable te_th         : WTheory.theory_uc;
  (*---*) te_known_w3   : w3_known_op Hp.t;
  mutable tk_known_w3   : (kpattern * w3_known_op) list;
  (*---*) te_ty         : w3ty Hp.t;
  (*---*) te_op         : w3op Hp.t;
  (*---*) te_lc         : w3op Hid.t;
  mutable te_lam        : WTerm.term Mta.t;
  mutable count_lam     : int;
  mutable count_ho      : int;
  (*---*) te_gen        : WTerm.term Hf.t;
  (*---*) te_xpath      : WTerm.lsymbol Hx.t;  (* proc and global var *)
  (*---*) te_absmod     : w3absmod Hid.t;      (* abstract module     *)
  (*---*) ts_mem        : WTy.tysymbol;
  (*---*) ts_distr      : WTy.tysymbol;
  (*---*) fs_witness    : WTerm.lsymbol;
  (*---*) fs_mu         : WTerm.lsymbol;
}

let empty_tenv env th ts_mem ts_distr fs_witness fs_mu =
  { te_env        = env;
    te_th         = th;
    te_known_w3   = Hp.create 0;
    tk_known_w3   = [];
    te_ty         = Hp.create 0;
    te_op         = Hp.create 0;
    te_lc         = Hid.create 0;
    te_lam        = Mta.empty;
    count_lam     = 0;
    count_ho      = 0;
    te_gen        = Hf.create 0;
    te_xpath      = Hx.create 0;
    te_absmod     = Hid.create 0;
    ts_mem                      ;
    ts_distr                    ;
    fs_witness                  ;
    fs_mu
  }

(* -------------------------------------------------------------------- *)
type lenv = {
  le_lv : WTerm.vsymbol Mid.t;
  le_tv : WTy.ty Mid.t;
  le_mt : EcMemory.memtype Mid.t;
}

let empty_lenv : lenv =
  { le_tv = Mid.empty; le_lv = Mid.empty; le_mt = Mid.empty }

let get_memtype lenv m =
  try Mid.find m lenv.le_mt with Not_found -> assert false

(* -------------------------------------------------------------------- *)
let str_p p =
  WIdent.id_fresh (String.map (function '.' -> '_' | c -> c) p)

let preid    id = WIdent.id_fresh (EcIdent.name id)
let preid_p  p  = str_p (EcPath.tostring p)
let preid_mp mp = str_p (EcPath.m_tostring mp)
let preid_xp xp = str_p (EcPath.x_tostring xp)

(* -------------------------------------------------------------------- *)
module Cast = struct
  let prop_of_bool t =
    assert (WTy.oty_equal t.WTerm.t_ty (Some WTy.ty_bool));
    match t.WTerm.t_node with
    | WTerm.Tif (t1, t2, t3) when
        WTerm.t_equal t2 WTerm.t_bool_true
        && WTerm.t_equal t3 WTerm.t_bool_false -> t1

    | _ when WTerm.t_equal t WTerm.t_bool_true  -> WTerm.t_true
    | _ when WTerm.t_equal t WTerm.t_bool_false -> WTerm.t_false

    | _ -> WTerm.t_equ t WTerm.t_bool_true

  let bool_of_prop t =
    assert (EcUtils.is_none t.WTerm.t_ty);
    match t.WTerm.t_node with
    | WTerm.Ttrue  -> WTerm.t_bool_true
    | WTerm.Tfalse -> WTerm.t_bool_false

    | WTerm.Tapp(ls, [t; tt]) when
        WTerm.t_equal tt WTerm.t_bool_true
        && WTerm.ls_equal ls WTerm.ps_equ -> t

    | _ ->
      WTerm.t_if t WTerm.t_bool_true WTerm.t_bool_false

  let force_prop t =
    if is_none t.WTerm.t_ty then t else prop_of_bool t

  let force_bool t =
    if is_none t.WTerm.t_ty then bool_of_prop t else t

  let merge_if w1 w2 =
    if w1.WTerm.t_ty = None then w1, force_prop w2
    else if w2.WTerm.t_ty = None then prop_of_bool w1, w2
    else w1, w2

  let merge_branches lw =
    if List.exists (fun (_,w) -> is_none w.WTerm.t_ty) lw then
      List.map (fun (p,w) -> p, force_prop w) lw
    else lw

  let arg a ty =
    match a.WTerm.t_ty, ty with
    | None  , None   -> a
    | None  , Some _ -> force_bool a
    | Some _, None   -> force_prop a
    | Some _, Some _ -> a

  let app mk args targs tres = mk (List.map2 arg args targs) tres

end

(* -------------------------------------------------------------------- *)
(* Create why3 tuple theory with projector                              *)

module Tuples = struct
  let ts = Hint.memo 17 (fun n ->
      let vl = ref [] in
      for _ = 1 to n do
        vl := WTy.create_tvsymbol (WIdent.id_fresh "a") :: !vl done;
      WTy.create_tysymbol (WIdent.id_fresh (Format.sprintf "tuple%d" n)) !vl WTy.NoDef)

  let proj = Hdint.memo 17 (fun (n, k) ->
      assert (0 <= k && k < n);
      let ts = ts n in
      let tl = List.map WTy.ty_var ts.WTy.ts_args in
      let ta = WTy.ty_app ts tl in
      let tr = List.nth tl k in
      let id = WIdent.id_fresh (Format.sprintf "proj%d_%d" n k) in
      WTerm.create_fsymbol ~proj:true id [ta] tr)

  let fs = Hint.memo 17 (fun n ->
      let ts = ts n in
      let tl = List.map WTy.ty_var ts.WTy.ts_args in
      let ty = WTy.ty_app ts tl in
      let id = WIdent.id_fresh (Format.sprintf "Tuple%d" n) in
      WTerm.create_fsymbol ~constr:1 id tl ty)

  let theory = Hint.memo 17 (fun n ->
      let ts = ts n and fs = fs n in
      let pl = List.mapi (fun i _ -> Some (proj (n, i))) ts.WTy.ts_args in
      let uc =
        let name = Format.sprintf "Tuple%d" n in
        WTheory.create_theory ~path:["Easycrypt"] (WIdent.id_fresh name)  in
      let uc = WTheory.add_data_decl uc [ts, [fs, pl]] in
      WTheory.close_theory uc)

end

let use th1 th2 =
  let name = th2.WTheory.th_name in
  WTheory.close_scope
    (WTheory.use_export (WTheory.open_scope th1 name.WIdent.id_string) th2)
    ~import:true

let load_tuple genv n =
  genv.te_th <- use genv.te_th (Tuples.theory n)

let wty_tuple genv targs =
  let len = List.length targs in
  load_tuple genv len;
  WTy.ty_app (Tuples.ts len) targs

let wfs_tuple genv nargs =
  load_tuple genv nargs;
  Tuples.fs nargs

let wt_tuple genv args =
  let len = List.length args in
  load_tuple genv len;
  let ty = WTy.ty_app (Tuples.ts len) (List.map WTerm.t_type args) in
  WTerm.fs_app (Tuples.fs len) args ty

let wproj_tuple genv arg i =
  let wty  = oget (arg.WTerm.t_ty) in
  let n =
    match wty.WTy.ty_node with
    | WTy.Tyapp (s, targs) ->
      let n = List.length targs in
      assert (Why3.Ty.ts_equal s (Tuples.ts n));
      n
    | _ -> assert false in
  load_tuple genv n;
  let fs = Tuples.proj (n,i) in
  WTerm.t_app_infer fs [arg]

let wfst genv arg = wproj_tuple genv arg 0
let wsnd genv arg = wproj_tuple genv arg 1

(* -------------------------------------------------------------------- *)
let trans_tv lenv id = oget (Mid.find_opt id lenv.le_tv)

(* -------------------------------------------------------------------- *)
let lenv_of_tparams ts =
  let trans_tv env ((id, _) : ty_param) = (* FIXME: TC HOOK *)
    let tv = WTy.create_tvsymbol (preid id) in
    { env with le_tv = Mid.add id (WTy.ty_var tv) env.le_tv }, tv
  in
  List.map_fold trans_tv empty_lenv ts

let lenv_of_tparams_for_hyp genv ts =
  let trans_tv env ((id, _) : ty_param) = (* FIXME: TC HOOK *)
    let ts = WTy.create_tysymbol (preid id) [] WTy.NoDef in
    genv.te_th <- WTheory.add_ty_decl genv.te_th ts;
    { env with le_tv = Mid.add id (WTy.ty_app ts []) env.le_tv }, ts
  in
  List.map_fold trans_tv empty_lenv ts

(* -------------------------------------------------------------------- *)
let instantiate tparams ~textra targs tres tys =
  let mtv =
    List.fold_left2
      (fun mtv tv ty -> WTy.Mtv.add tv ty mtv)
      WTy.Mtv.empty tparams tys in
  let textra = List.map (WTy.ty_inst mtv) textra in
  let targs = List.map (some |- WTy.ty_inst mtv) targs in
  let tres  = tres |> omap (WTy.ty_inst mtv) in
  (textra, targs, tres)

(* -------------------------------------------------------------------- *)
let plain_w3op ?(name = "x") tparams ls = {
  w3op_fo = `LDecl ls;
  w3op_ta = instantiate tparams ~textra:[] ls.WTerm.ls_args ls.WTerm.ls_value;
  w3op_ho = `HO_TODO (name, ls.WTerm.ls_args, ls.WTerm.ls_value);
}

let prop_w3op ?(name = "x") arity mkfo =
  let dom  = List.make arity None in
  let hdom = List.make arity WTy.ty_bool in

  { w3op_fo = `Internal mkfo;
    w3op_ta = (fun _ -> [], dom, None);
    w3op_ho = `HO_TODO (name, hdom, None); }

let w3op_as_ldecl = function
  | `LDecl ls -> ls | _ -> assert false

let w3op_as_internal = function
  | `Internal mk -> mk | _ -> assert false

let w3op_fo w3op =
  match w3op.w3op_fo with
  | `Internal mk -> mk
  | `LDecl    ls -> WTerm.t_app ls

(* -------------------------------------------------------------------- *)
let mk_tglob genv mp =
  assert (mp.EcPath.m_args = []);
  let id = EcPath.mget_ident mp in
  match Hid.find_opt genv.te_absmod id with
  | Some { w3am_ty } -> w3am_ty
  | None ->
    (* create the type symbol *)
    let pid = preid id in
    let ts = WTy.create_tysymbol pid [] WTy.NoDef in
    genv.te_th <- WTheory.add_ty_decl genv.te_th ts;
    let ty = WTy.ty_app ts [] in
    Hid.add genv.te_absmod id { w3am_ty = ty };
    ty

(* -------------------------------------------------------------------- *)
let rec trans_ty ((genv, lenv) as env) ty =
  match ty.ty_node with
  | Tglob   mp -> trans_tglob env mp
  | Tunivar _ -> assert false
  | Tvar    x -> trans_tv lenv x
  | Ttuple  ts-> wty_tuple genv (trans_tys env ts)

  | Tconstr (p, tys) ->
    let id = trans_pty genv p in
    WTy.ty_app id (trans_tys env tys)

  | Tfun (t1, t2) ->
    WTy.ty_func (trans_ty env t1) (trans_ty env t2)

and trans_tglob ((genv, _lenv) as env) mp =
  let ty =
    NormMp.norm_tglob genv.te_env mp
  in
  match ty.ty_node with
  | Tglob mp -> mk_tglob genv mp
  | _ -> trans_ty env ty

and trans_tys env tys = List.map (trans_ty env) tys

and trans_pty genv p =
  match Hp.find_opt genv.te_ty p with
  | Some tv -> tv
  | None    ->
    trans_tydecl genv (p, EcEnv.Ty.by_path p genv.te_env)

and trans_tydecl genv (p, tydecl) =
  let pid = preid_p p in
  let lenv, tparams = lenv_of_tparams tydecl.tyd_params in

  let ts, opts, decl =
    match tydecl.tyd_type with
    | `Abstract _ ->
      let ts = WTy.create_tysymbol pid tparams WTy.NoDef in
      (ts, [], WDecl.create_ty_decl ts)

    | `Concrete ty ->
      let ty = trans_ty (genv, lenv) ty in
      let ts = WTy.create_tysymbol pid tparams (WTy.Alias ty) in
      (ts, [], WDecl.create_ty_decl ts)

    | `Datatype dt ->
      let ncs  = List.length dt.tydt_ctors in
      let ts   = WTy.create_tysymbol pid tparams WTy.NoDef in

      Hp.add genv.te_ty p ts;

      let wdom = tconstr p (List.map (tvar |- fst) tydecl.tyd_params) in
      let wdom = trans_ty (genv, lenv) wdom in

      let for_ctor (c, ctys) =
        let wcid  = pqoname (prefix p) c in
        let wctys = List.map (trans_ty (genv, lenv)) ctys in
        let wcls  = WTerm.create_lsymbol ~constr:ncs (preid_p wcid) wctys (Some wdom) in
        let w3op  = plain_w3op ~name:c tparams wcls in
        ((wcid, w3op), (wcls, List.make (List.length ctys) None)) in

      let opts, wdtype = List.split (List.map for_ctor dt.tydt_ctors) in

      (ts, opts, WDecl.create_data_decl [ts, wdtype])

    | `Record (_, rc) ->
      let ts = WTy.create_tysymbol pid tparams WTy.NoDef in

      Hp.add genv.te_ty p ts;

      let wdom  = tconstr p (List.map (tvar |- fst) tydecl.tyd_params) in
      let wdom  = trans_ty (genv, lenv) wdom in

      let for_field (fname, fty) =
        let wfid  = pqoname (prefix p) fname in
        let wfty  = trans_ty (genv, lenv) fty in
        let wcls  = WTerm.create_lsymbol ~proj:true (preid_p wfid) [wdom] (Some wfty) in
        let w3op  = plain_w3op ~name:fname tparams wcls in
        ((wfid, w3op), wcls)
      in

      let wcid  = EI.record_ctor_path p in
      let wctys = List.map (trans_ty (genv, lenv)) (List.map snd rc) in
      let wcls  = WTerm.create_lsymbol ~constr:1 (preid_p wcid) wctys (Some wdom) in
      let w3op  = plain_w3op ~name:(basename wcid) tparams wcls in

      let opts, wproj = List.split (List.map for_field rc) in
      let wproj = List.map some wproj in

      (ts, (wcid, w3op) :: opts, WDecl.create_data_decl [ts, [wcls, wproj]])

  in

  genv.te_th <- WTheory.add_decl genv.te_th decl;
  Hp.add genv.te_ty p ts;
  List.iter (fun (p, wop) -> Hp.add genv.te_op p wop) opts;
  ts

(* -------------------------------------------------------------------- *)
let trans_memtype ((genv, _) as env) mt =
  let ty_mem = WTy.ty_app genv.ts_mem [] in
  match EcMemory.local_type mt with
  | None -> ty_mem
  | Some ty ->
    let ty = trans_ty env ty in
    wty_tuple genv [ty; ty_mem]

(* -------------------------------------------------------------------- *)
exception CanNotTranslate

let trans_binding genv lenv (x, xty) =
  let lenv, wty =
    match xty with
    | GTty ty ->
      lenv, trans_ty (genv, lenv) ty
    | GTmem mt ->
      { lenv with le_mt = Mid.add x mt lenv.le_mt }, trans_memtype (genv, lenv) mt

    | _ -> raise CanNotTranslate
  in
  let wvs = WTerm.create_vsymbol (preid x) wty in
  ({ lenv with le_lv = Mid.add x wvs lenv.le_lv }, wvs)

(* -------------------------------------------------------------------- *)
let trans_bindings genv lenv bds =
  List.map_fold (trans_binding genv) lenv bds

(* -------------------------------------------------------------------- *)
let trans_lvars genv lenv bds =
  trans_bindings genv lenv (List.map (snd_map gtty) bds)

(* -------------------------------------------------------------------- *)
(* build the higher-order symbol and add the corresponding axiom.       *)
let mk_highorder_symb genv ids dom codom =
  let name = ids ^ "_ho_" ^ string_of_int genv.count_ho in
  let pid = WIdent.id_fresh name in
  let ty = List.fold_right WTy.ty_func dom (odfl WTy.ty_bool codom) in
  WTerm.create_fsymbol pid [] ty, ty

let mk_highorder_func genv ids dom codom mk =
  let ls', ty = mk_highorder_symb genv ids dom codom in
  let decl' = WDecl.create_param_decl ls' in
  let name = ids ^ "_ho_spec" ^ string_of_int genv.count_ho in
  genv.count_ho <- genv.count_ho + 1;
  let pid_spec = WIdent.id_fresh name in
  let pr = WDecl.create_prsymbol pid_spec in
  let preid = WIdent.id_fresh "x" in
  let params = List.map (WTerm.create_vsymbol preid) dom in
  let args = List.map WTerm.t_var params in
  let f_app' =
    List.fold_left WTerm.t_func_app (WTerm.fs_app ls' [] ty) args in
  let f_app = mk args codom in
  let spec =
    match codom with
    | None -> WTerm.t_iff (Cast.force_prop f_app') f_app
    | Some _ -> WTerm.t_equ f_app' f_app in
  let spec = WTerm.t_forall_close params [] spec in
  let decl_s = WDecl.create_prop_decl WDecl.Paxiom pr spec in
  (ls',decl',decl_s)

(* -------------------------------------------------------------------- *)
let w3op_ho_lsymbol genv wop =
  match wop.w3op_ho with
  | `HO_DONE ls -> ls

  | `HO_TODO (id, dom, codom) ->
    let ls, decl, decl_s = mk_highorder_func genv id dom codom (w3op_fo wop) in
    genv.te_th <- WTheory.add_decl genv.te_th decl;
    genv.te_th <- WTheory.add_decl genv.te_th decl_s;
    wop.w3op_ho <- `HO_DONE ls; ls

  | `HO_FIX (ls, _, _, r) ->
    r := true; ls

(* -------------------------------------------------------------------- *)
let rec highorder_type targs tres =
  match targs with
  | [] -> odfl WTy.ty_bool tres
  | a::targs -> WTy.ty_func (odfl WTy.ty_bool a) (highorder_type targs tres)

let apply_highorder f args =
  List.fold_left (fun f a -> WTerm.t_func_app f (Cast.force_bool a)) f args

let apply_wop genv wop tys args =
  let (textra, targs, tres) = wop.w3op_ta tys in
  let w_witness ty = WTerm.fs_app genv.fs_witness [] ty in
  let eargs = List.map w_witness textra in
  let arity = List.length targs in
  let nargs = List.length args in

  let targs = List.map some textra @ targs in
  if nargs = arity then Cast.app (w3op_fo wop) (eargs @ args) targs tres
  else if nargs < arity then
    let fty = highorder_type targs tres in
    let ls' = w3op_ho_lsymbol genv wop in
    apply_highorder (WTerm.fs_app ls' [] fty) (eargs @ args)
  else (* arity < nargs : too many arguments *)
    let args1,args2 = List.takedrop arity args in
    apply_highorder (Cast.app (w3op_fo wop) (eargs @ args1) targs tres) args2


(* -------------------------------------------------------------------- *)
let trans_lambda genv wvs wbody =
  try Mta.find (wvs,wbody) genv.te_lam with Not_found ->
    (* We compute the free variable of the lambda *)
    let fv     =
      List.fold_left (fun s x -> WTerm.Mvs.remove x s)
        (WTerm.t_vars wbody) wvs in
    let fv_ids = WTerm.Mvs.keys fv in
    let tfv = List.map (fun v -> v.WTerm.vs_ty) fv_ids in
    let tvs = List.map (fun v -> v.WTerm.vs_ty) wvs in
    let codom =
      if wbody.WTerm.t_ty = None then WTy.ty_bool
      else oget wbody.WTerm.t_ty in
    (* We create the symbol corresponding to the lambda *)
    let name = "unamed_lambda_" ^ string_of_int genv.count_lam in
    let lam_sym = WIdent.id_fresh name in
    let flam_sym =
      WTerm.create_fsymbol lam_sym tfv
        (List.fold_right WTy.ty_func tvs codom) in
    let decl_sym = WDecl.create_param_decl flam_sym in
    (* We create the spec *)
    let fvargs   = List.map WTerm.t_var fv_ids in
    let vsargs   = List.map WTerm.t_var wvs in
    let flam_app =
      WTerm.t_app_infer flam_sym fvargs in
    let flam_fullapp =
      List.fold_left WTerm.t_func_app flam_app vsargs in
    let concl =
      if wbody.WTerm.t_ty = None then
        WTerm.t_iff (Cast.force_prop flam_fullapp) wbody
      else WTerm.t_equ flam_fullapp wbody in
    let spec = WTerm.t_forall_close (fv_ids@wvs) [] concl in
    let name = "unamed_lambda_spec_" ^ string_of_int genv.count_lam in
    genv.count_lam <- genv.count_lam + 1;
    let spec_sym =
      WDecl.create_prsymbol (WIdent.id_fresh name) in
    let decl_spec = WDecl.create_prop_decl WDecl.Paxiom spec_sym spec in
    genv.te_th <- WTheory.add_decl genv.te_th decl_sym;
    genv.te_th <- WTheory.add_decl genv.te_th decl_spec;
    genv.te_lam  <- Mta.add (wvs,wbody) flam_app genv.te_lam;
    flam_app

(* -------------------------------------------------------------------- *)
module E = struct
  exception MFailure

  let kmatch k f =
    let rec doit (acc : form list) (k : kpattern) (f : form) =
      match k, fst_map f_node (destr_app f) with
      | KHole, _ ->
        f :: acc

      | KProj (sk, i), (Fproj (sf, j), []) when i = j ->
        doit acc sk sf

      | KApp (sp, ks), (Fop (p, _), fs)
        when EcPath.p_equal sp p && List.length ks = List.length fs
        -> List.fold_left2 doit acc ks fs

      | _, _ -> raise MFailure
    in
    try Some (List.rev (doit [] k f)) with MFailure -> None

  let trans_kpattern env (k, (ls, wth)) f =
    match kmatch k f with
    | Some args ->
      let dom, codom = List.map f_ty args, f.f_ty in

      let wdom   = trans_tys env dom in
      let wcodom =
        if   ER.EqTest.is_bool (fst env).te_env codom
        then None
        else Some (trans_ty env codom) in

      let w3op =
        let name = ls.WTerm.ls_name.WIdent.id_string in
        { w3op_fo = `LDecl ls;
          w3op_ta = instantiate [] ~textra:[] wdom wcodom;
          w3op_ho = `HO_TODO (name, wdom, wcodom); }
      in
      Some (w3op,args)
    | None -> None

  let trans_kpatterns env (ks : (kpattern * w3_known_op) list) (f : form) trans_form =
    let w3op,args =
      EcUtils.oget ~exn:CanNotTranslate
        (List.Exceptionless.find_map (fun k -> trans_kpattern env k f) ks)
    in
    let wargs = List.map (trans_form env) args in
    apply_wop (fst env) w3op [] wargs
end

(* -------------------------------------------------------------------- *)
let rec trans_form ((genv, lenv) as env : tenv * lenv) (fp : form) =
  try
    let w3op,args =
      EcUtils.oget ~exn:CanNotTranslate
        (List.Exceptionless.find_map (fun k -> E.trans_kpattern env k fp)
           genv.tk_known_w3)
    in
    let wargs = List.map (trans_form env) args in
    apply_wop (fst env) w3op [] wargs
  with CanNotTranslate ->
  match fp.f_node with
  | Fquant (qt, bds, body) ->
    begin
      try
        let lenv, wbds = trans_bindings genv lenv bds in
        let wbody = trans_form (genv,lenv) body in
        (match qt with
         | Lforall -> WTerm.t_forall_close wbds [] (Cast.force_prop wbody)
         | Lexists -> WTerm.t_exists_close wbds [] (Cast.force_prop wbody)
         | Llambda -> trans_lambda genv wbds wbody)
      with CanNotTranslate -> trans_gen env fp
    end

  | Fint n -> WTerm.t_int_const (BI.to_why3 n)
  | Fif    _ -> trans_app env fp []
  | Fmatch _ -> trans_app env fp []
  | Flet   _ -> trans_app env fp []
  | Flocal _ -> trans_app env fp []
  | Fop    _ -> trans_app env fp []

  (* Special case for `%r` *)
  | Fapp({ f_node = Fop (p, [])},  [{f_node = Fint n}])
    when p_equal p CI_Real.p_real_of_int ->
    WTerm.t_real_const (BI.to_why3 n)

  | Fapp (f,args) ->
    trans_app env f (List.map (trans_form env) args)

  | Ftuple args   -> wt_tuple genv (List.map (trans_form_b env) args)

  | Fproj (tfp,i) -> wproj_tuple genv (trans_form env tfp) i

  | Fpvar(pv,mem) ->
    trans_pvar env pv fp.f_ty mem

  | Fglob (m,mem) -> trans_glob env m mem

  | Fpr pr        -> trans_pr env pr

  | Fcoe _
  | FeagerF _
  | FhoareF  _  | FhoareS   _
  | FcHoareF  _ | FcHoareS   _
  | FbdHoareF _ | FbdHoareS _
  | FequivF   _ | FequivS   _
    -> trans_gen env fp

and trans_form_b env f = Cast.force_bool (trans_form env f)

(* -------------------------------------------------------------------- *)
and trans_app  ((genv, lenv) as env : tenv * lenv) (f : form) args =
  match f.f_node with
  | Fquant (Llambda, bds, body) ->
    trans_fun env bds body args

  | Fop (p, ts) ->
    let wop = trans_op genv p in
    let tys = List.map (trans_ty (genv,lenv)) ts in
    apply_wop genv wop tys args

  | Flocal x when Hid.mem genv.te_lc x ->
    apply_wop genv (Hid.find genv.te_lc x) [] args

  | Flocal x ->
    let t =  WTerm.t_var (oget (Mid.find_opt x lenv.le_lv)) in
    apply_highorder t args

  | Flet (lp, f1, f2) ->
    trans_letbinding env (lp, f1, f2) args

  | Fif (fb, ft, ff) ->
    let wb = trans_form env fb in
    let wt = trans_app env ft args in
    let wf = trans_app env ff args in
    let wt, wf = Cast.merge_if wt wf in
    WTerm.t_if_simp (Cast.force_prop wb) wt wf

  | Fmatch (fb, bs, _ty) ->
    let p, dty, tvs = oget (EcEnv.Ty.get_top_decl fb.f_ty genv.te_env) in
    let dty = oget (EcDecl.tydecl_as_datatype dty) in
    let bs = List.combine bs dty.tydt_ctors in

    let wfb = trans_form env fb in
    let wbs = List.map (trans_branch env (p, dty, tvs)) bs in
    let wbs = Cast.merge_branches wbs in
    WTerm.t_case_close_simp wfb wbs

  | Fapp (f, args') ->
    let args' = List.map (trans_form env) args' in
    trans_app env f (args'@args)

  | _ ->
    apply_highorder (trans_form env f) args

(* -------------------------------------------------------------------- *)
and trans_branch (genv, lenv) (p, _dty, tvs) (f, (cname, argsty)) =
  let nargs = List.length argsty in
  let xs, f =
    let xs, f = decompose_lambda f in
    let xs1, xs2 = List.split_at nargs xs in
    let xs1 = List.map (snd_map gty_as_ty) xs1 in
    (xs1, f_lambda xs2 f) in
  let csymb = EcPath.pqoname (EcPath.prefix p) cname in
  let csymb =
    match (trans_op genv csymb).w3op_fo with
    | `LDecl csymb -> csymb | _ -> assert false
  in

  let lenv, ws = trans_lvars genv lenv xs in
  let wcty = trans_ty (genv, lenv) (tconstr p tvs) in
  let ws = List.map WTerm.pat_var ws in
  let ws = WTerm.pat_app csymb ws wcty in
  let wf = trans_app (genv, lenv) f [] in

  (ws, wf)

(* -------------------------------------------------------------------- *)
and trans_fun (genv, lenv) bds body args =
  let lbds  = List.length bds in
  let largs = List.length args in

  if lbds <= largs then
    let lenv, wbds = trans_bindings genv lenv bds in
    if lbds = largs then
      w_t_lets wbds args (trans_form (genv, lenv) body)
    else (* lbds < largs *)
      let args1, args2 = List.takedrop lbds args in
      w_t_lets wbds args1 (trans_app (genv,lenv) body args2)
  else (* largs < lbds *)
    let bds1, bds2 = List.takedrop largs bds in
    let lenv, wbds1 = trans_bindings genv lenv bds1 in
    w_t_lets wbds1 args (trans_form (genv,lenv) (f_lambda bds2 body))

(* -------------------------------------------------------------------- *)
and trans_letbinding (genv, lenv) (lp, f1, f2) args =
  let w1 = trans_form_b (genv, lenv) f1 in
  match lp with
  | LSymbol (id, ty) ->
    let lenv, vs = trans_binding genv lenv (id,gtty ty) in
    let w2 = trans_app (genv,lenv) f2 args in
    w_t_let vs w1 w2

  | LTuple ids ->
    let nids = List.length ids in
    let lenv, vs = trans_lvars genv lenv ids in
    let pat =
      WTerm.pat_app (wfs_tuple genv nids)
        (List.map WTerm.pat_var vs) (WTerm.t_type w1) in
    let w2 = trans_app (genv, lenv) f2 args in
    let br = WTerm.t_close_branch pat w2 in
    WTerm.t_case w1 [br]

  | LRecord (p,ids) ->
    (*  ignore (trans_ty (genv,lenv) f1.f_ty); *)
    let p = EI.record_ctor_path p in
    let ids = List.map (fst_map (ofdfl (fun _ -> EcIdent.create "_"))) ids in
    let lenv, vs = trans_lvars genv lenv ids in
    let ls = w3op_as_ldecl (trans_op genv p).w3op_fo in
    let pat = WTerm.pat_app ls (List.map WTerm.pat_var vs) (WTerm.t_type w1) in
    let w2 = trans_app (genv,lenv) f2 args in
    let br = WTerm.t_close_branch pat w2 in
    WTerm.t_case w1 [br]

(* -------------------------------------------------------------------- *)
and trans_pvar ((genv, lenv) as env) pv ty mem =
  let pv = NormMp.norm_pvar genv.te_env pv in
  let mt = get_memtype lenv mem in
  match pv with
  | PVloc x ->
    let m = trans_mem env ~forglobal:false mem in
    begin match EcMemory.lookup x mt with
      | Some (_,_,Some i) -> wproj_tuple genv m i
      | Some (_,_,None)   -> m
      | None              -> assert false
    end
  | PVglob xp ->
    let m =  trans_mem env ~forglobal:true mem in
    let ls =
      match Hx.find_opt genv.te_xpath xp with
      | Some ls -> ls
      | None ->
        let ty = Some (trans_ty env ty) in
        let pid = preid_xp xp in
        let ty_mem = WTy.ty_app genv.ts_mem [] in
        let ls = WTerm.create_lsymbol pid [ty_mem] ty in
        genv.te_th <- WTheory.add_param_decl genv.te_th ls;
        Hx.add genv.te_xpath xp ls; ls
    in
    WTerm.t_app_infer ls [m]

(* -------------------------------------------------------------------- *)
and trans_glob ((genv, _) as env) mp mem =
  let f = NormMp.norm_glob genv.te_env mem mp in
  match f.f_node with
  | Fglob (mp, mem) ->
    assert (mp.EcPath.m_args = []);

    let id   = EcPath.mget_ident mp in
    let wmem = trans_mem env ~forglobal:true mem in
    let w3op =
      match Hid.find_opt genv.te_lc id with
      | Some w3op -> w3op
      | None ->
        let ty  = Some (mk_tglob genv mp) in
        let pid = preid id in
        let ty_mem = WTy.ty_app genv.ts_mem [] in
        let ls  = WTerm.create_lsymbol pid [ty_mem] ty in
        let w3op =
          { w3op_fo = `LDecl ls;
            w3op_ta = (fun _tys -> [], [Some ty_mem], ty);
            w3op_ho = `HO_TODO (EcIdent.name id, [ty_mem], ty); } in
        genv.te_th <- WTheory.add_param_decl genv.te_th ls;
        Hid.add genv.te_lc id w3op;
        w3op
    in apply_wop genv w3op [] [wmem]

  | _ -> trans_form env f

(* -------------------------------------------------------------------- *)
and trans_mem (genv,lenv) ~forglobal mem =
  let wmem =
    match Hid.find_opt genv.te_lc mem with
    | Some w3op -> apply_wop genv w3op [] []
    | None -> WTerm.t_var (oget (Mid.find_opt mem lenv.le_lv)) in
  let mt = get_memtype lenv mem in
  let has_locals = EcMemory.has_locals mt in
  if forglobal then
    if has_locals then wsnd genv wmem
    else wmem
  else
    (assert has_locals; wfst genv wmem)

(* -------------------------------------------------------------------- *)
and trans_pr ((genv,lenv) as env) {pr_mem; pr_fun; pr_args; pr_event} =
  let wmem = trans_mem env ~forglobal:true pr_mem in
  let warg = trans_form_b env pr_args in

  (* Translate the procedure *)
  let xp = NormMp.norm_xfun genv.te_env pr_fun in
  let _, mt = EcEnv.Fun.prF_memenv mhr pr_fun genv.te_env in
  let mty = trans_memtype env mt in
  let tyr = WTy.ty_app genv.ts_distr [mty] in
  let ls =
    let trans () =
      let tya = oget warg.WTerm.t_ty in
      let tyr = Some tyr in
      let pid = preid_xp xp in
      let ty_mem = WTy.ty_app genv.ts_mem [] in
      let ls  = WTerm.create_lsymbol pid [tya; ty_mem] tyr in
      genv.te_th <- WTheory.add_param_decl genv.te_th ls;
      Hx.add genv.te_xpath xp ls;
      ls
    in Hx.find_opt genv.te_xpath xp |> ofdfl trans
  in

  let d = WTerm.t_app ls [warg; wmem] (Some tyr) in

  let wev =
    let lenv, wbd = trans_binding genv lenv (mhr, GTmem mt) in
    let wbody = trans_form_b (genv,lenv) pr_event in
    trans_lambda genv [wbd] wbody

  in WTerm.t_app_infer genv.fs_mu [d; wev]

(* -------------------------------------------------------------------- *)
and trans_gen ((genv, _) as env :  tenv * lenv) (fp : form) =
  match Hf.find_opt genv.te_gen fp with
  | None ->
    let name = WIdent.id_fresh "x" in
    let wty  =
      if   EcReduction.EqTest.is_bool genv.te_env fp.f_ty
      then None
      else Some (trans_ty env fp.f_ty) in

    let lsym = WTerm.create_lsymbol name [] wty in
    let term = WTerm.t_app_infer lsym [] in

    genv.te_th <- WTheory.add_param_decl genv.te_th lsym;
    Hf.add genv.te_gen fp term;
    term

  | Some term -> term

(* -------------------------------------------------------------------- *)
and trans_body (genv, lenv) wdom wcodom topbody =
  let bds, body = decompose_lambda topbody in
  let lbds  = List.length bds  in
  let lwdom = List.length wdom in

  let params, body =
    if lbds = lwdom then
      let lenv, params = trans_bindings genv lenv bds in
      params, trans_form (genv, lenv) body
    else
      let preid  = WIdent.id_fresh "x" in
      let params = List.map (WTerm.create_vsymbol preid) wdom in
      let args   = List.map WTerm.t_var params in
      params, trans_app (genv, lenv) topbody args in
  let body = Cast.arg body wcodom in
  let body =
    match wcodom, body.WTerm.t_ty with
    | None  , Some _ -> Cast.force_prop body
    | Some _, None   -> Cast.force_bool body
    | _, _ -> body

  in (params, body)

(* -------------------------------------------------------------------- *)
and trans_fix (genv, lenv) (wdom, o) =
  let (lenv, vs) = trans_lvars genv lenv o.opf_args in
  let pterm   = List.map (List.nth vs) (fst o.opf_struct) in
  let ptermty = List.map (fun x -> x.WTerm.vs_ty) pterm in
  let ptermc  = List.length ptermty in

  let eparams =
    let preid = WIdent.id_fresh "x" in
    List.map (WTerm.create_vsymbol preid) (List.drop (List.length vs) wdom) in

  let eargs = List.map WTerm.t_var eparams in

  let ptns =
    let rec compile ptns (ctors, m) =
      match m with
      | OPB_Branch bs ->
        Parray.fold_left
          (fun ptns b ->
             let cl = oget (Hp.find_opt genv.te_op (fst b.opb_ctor)) in
             let cl = w3op_as_ldecl cl.w3op_fo in
             compile ptns (cl :: ctors, b.opb_sub))
          ptns bs

      | OPB_Leaf (locals, e) ->
        let ctors = List.rev ctors in
        let lenv, cvs = List.map_fold (trans_lvars genv) lenv locals in
        let fe = EcCoreFol.form_of_expr EcCoreFol.mhr e in

        let we = trans_app (genv, lenv) fe eargs in

        let ptn =
          let for1 (cl, cvs) pty =
            let ptn = List.map WTerm.pat_var cvs in
            let ptn = WTerm.pat_app cl ptn pty in
            ptn
          in
          try  List.map2 for1 (List.combine ctors cvs) ptermty
          with Failure _ -> assert false
        in

        let ptn =
          if   ptermc > 1
          then WTerm.pat_app (wfs_tuple genv ptermc) ptn (wty_tuple genv ptermty)
          else oget (List.ohead ptn)
        in (ptn, we) :: ptns

    in compile [] ([], o.opf_branches)
  in

  let ptns = Cast.merge_branches ptns in
  let ptns =
    List.rev_map
      (fun (p, e) -> WTerm.t_close_branch p e)
      ptns in

  let mtch =
    if   ptermc > 1
    then wt_tuple genv (List.map WTerm.t_var pterm)
    else WTerm.t_var (oget (List.ohead pterm)) in

  let body = WTerm.t_case mtch ptns in

  (vs @ eparams, body)

(* -------------------------------------------------------------------- *)
and trans_op ?(body = true) (genv : tenv) p =

  (* FIXME: this is a ack for constructor, when the constructor is
   * translated before its type. Should the same be done for some
   * other kinds of operators, like projections? *)
  try Hp.find genv.te_op p with Not_found ->
    let op = EcEnv.Op.by_path p genv.te_env in
    let lenv, wparams = lenv_of_tparams op.op_tparams in
    let dom, codom = EcEnv.Ty.signature genv.te_env op.op_ty in
    let textra =
      List.filter (fun (tv,_) -> not (Mid.mem tv (Tvar.fv op.op_ty))) op.op_tparams
    in
    let textra =
      List.map (fun (tv,_) -> trans_ty (genv,lenv) (tvar tv)) textra
    in
    let wdom   = trans_tys (genv, lenv) dom in
    let wcodom =
      if   ER.EqTest.is_bool genv.te_env codom
      then None
      else Some (trans_ty (genv, lenv) codom)
    in

    let known, ls =
      match Hp.find_opt genv.te_known_w3 p with
      | Some (ls, th) -> (true, ls)
      | None ->
        let ls = WTerm.create_lsymbol (preid_p p) (textra@wdom) wcodom in
        (false, ls)
    in

    let w3op =
      let name = ls.WTerm.ls_name.WIdent.id_string in
      let w3op_ho =
        if EcDecl.is_fix op then
          let ls, decl, decl_s =
            mk_highorder_func genv name (textra@wdom) wcodom (WTerm.t_app ls)
          in
          `HO_FIX (ls, decl, decl_s, ref false)
        else
          `HO_TODO (name, textra@wdom, wcodom)
      in
      let w3op = { w3op_fo = `LDecl ls;
                   w3op_ta = instantiate wparams ~textra wdom wcodom;
                   w3op_ho; }
      in
      if known then Hp.add genv.te_op p w3op;
      w3op
    in

    let register = OneShot.mk (fun () -> Hp.add genv.te_op p w3op) in

    if not known then
      begin
        let wextra = List.map (fun ty ->
            WTerm.create_vsymbol (WIdent.id_fresh "_") ty) textra
        in
        let decl =
          match body, op.op_kind with
          | true, OB_oper (Some (OP_Plain (body, false))) ->
            let wparams, wbody = trans_body (genv, lenv) wdom wcodom body in
            WDecl.create_logic_decl [WDecl.make_ls_defn ls (wextra@wparams) wbody]

          | true, OB_oper (Some (OP_Fix ({ opf_nosmt = false } as body ))) ->
            OneShot.now register;
            let wparams, wbody = trans_fix (genv, lenv) (wdom, body) in
            let wbody = Cast.arg wbody ls.WTerm.ls_value in
            WDecl.create_logic_decl [WDecl.make_ls_defn ls (wextra@wparams) wbody]

          | true, OB_pred (Some (PR_Plain body)) ->
            let wparams, wbody = trans_body (genv, lenv) wdom None body in
            WDecl.create_logic_decl [WDecl.make_ls_defn ls (wextra@wparams) wbody]

          | _, _ ->  WDecl.create_param_decl ls
        in
        OneShot.now register;

        match w3op.w3op_ho with
        | `HO_FIX (ls, ho_decl, ho_decl_s, r) ->
          begin
            if !r then begin
              List.iter
                (fun d -> genv.te_th <- WTheory.add_decl genv.te_th d)
                [ho_decl; decl; ho_decl_s];
              w3op.w3op_ho <- `HO_DONE ls
            end else begin
              genv.te_th <- WTheory.add_decl genv.te_th decl;
              w3op.w3op_ho <-
                let name = ls.WTerm.ls_name.WIdent.id_string in
                `HO_TODO (name, textra@wdom, wcodom)
            end
          end
        | _ ->  genv.te_th <- WTheory.add_decl genv.te_th decl
      end;

    w3op

(* -------------------------------------------------------------------- *)
let add_axiom ((genv, _) as env) preid form =
  let w    = trans_form env form in
  let pr   = WDecl.create_prsymbol preid in
  let decl = WDecl.create_prop_decl WDecl.Paxiom pr (Cast.force_prop w) in
  genv.te_th <- WTheory.add_decl ~warn:false genv.te_th decl

(* -------------------------------------------------------------------- *)
let trans_hyp ((genv, lenv) as env) (x, ty) =
  match ty with
  | LD_var (ty, body) ->
    let dom, codom = EcEnv.Ty.signature genv.te_env ty in
    let wdom   = trans_tys env dom in
    let wcodom =
      if   ER.EqTest.is_bool genv.te_env codom
      then None
      else Some (trans_ty env codom) in

    let ls = WTerm.create_lsymbol (preid x) wdom wcodom in
    let w3op = {
      w3op_fo = `LDecl ls;
      w3op_ta = (fun _ -> ([], List.map some wdom, wcodom));
      w3op_ho = `HO_TODO (EcIdent.name x, wdom, wcodom);
    } in

    let decl =
      match body with
      | None -> WDecl.create_param_decl ls
      | Some body ->
        let wparams, wbody = trans_body env wdom wcodom body in
        let ld = WDecl.make_ls_defn ls wparams wbody in
        WDecl.create_logic_decl [ld]

    in
    genv.te_th <- WTheory.add_decl genv.te_th decl;
    Hid.add genv.te_lc x w3op;
    env

  | LD_hyp f ->
    (* FIXME: Selection of hypothesis *)
    add_axiom env (preid x) f;
    env

  | LD_mem    mt ->
    let wty = trans_memtype env mt in
    let lenv = { lenv with le_mt = Mid.add x mt lenv.le_mt } in
    let wcodom = Some wty in
    let ls =  WTerm.create_lsymbol (preid x) [] wcodom in
    let w3op = {
      w3op_fo = `LDecl ls;
      w3op_ta = (fun _ -> ([], [], wcodom));
      w3op_ho = `HO_TODO (EcIdent.name x, [], wcodom);
    } in

    genv.te_th <- WTheory.add_param_decl genv.te_th ls;
    Hid.add genv.te_lc x w3op;
    (genv, lenv)

  | LD_modty  _ -> env

  | LD_abs_st _ -> env

(* -------------------------------------------------------------------- *)
let lenv_of_hyps genv (hyps : hyps) : lenv =
  let lenv = fst (lenv_of_tparams_for_hyp genv hyps.h_tvar) in
  snd (List.fold_left trans_hyp (genv, lenv) (List.rev hyps.h_local))

(* -------------------------------------------------------------------- *)
let trans_axiom genv (p, ax) =
  (*  if not ax.ax_nosmt then *)
  let lenv,_ = lenv_of_tparams ax.ax_tparams in
  add_axiom (genv, lenv) (preid_p p) ax.ax_spec

(* -------------------------------------------------------------------- *)

let mk_predb1 f l _ = f (Cast.force_prop (as_seq1 l))
let mk_predb2 f l _ = curry f (t2_map Cast.force_prop (as_seq2 l))

let mk_true  = fun _ _ -> WTerm.t_true
let mk_false = fun _ _ -> WTerm.t_false
let mk_not   = mk_predb1 WTerm.t_not
let mk_anda  = mk_predb2 WTerm.t_and_asym
let mk_and   = mk_predb2 WTerm.t_and
let mk_ora   = mk_predb2 WTerm.t_or_asym
let mk_or    = mk_predb2 WTerm.t_or
let mk_imp   = mk_predb2 WTerm.t_implies
let mk_iff   = mk_predb2 WTerm.t_iff

let add_core_ops tenv =
  let core_ops = [
    (CI_Bool.p_true , "TRUE" , 0, mk_true );
    (CI_Bool.p_false, "FALSE", 0, mk_false);
    (CI_Bool.p_not  , "NOT"  , 1, mk_not  );
    (CI_Bool.p_and  , "AND"  , 2, mk_and  );
    (CI_Bool.p_anda , "ANDA" , 2, mk_anda );
    (CI_Bool.p_or   , "OR"   , 2, mk_or   );
    (CI_Bool.p_ora  , "ORA"  , 2, mk_ora  );
    (CI_Bool.p_imp  , "IMP"  , 2, mk_imp  );
    (CI_Bool.p_iff  , "IFF"  , 2, mk_iff  );
  ]
  in
  List.iter (fun (p, id, arity, fo) ->
      Hp.add tenv.te_op p (prop_w3op ~name:id arity fo))
    core_ops

let add_core_theory env task ((file,thy), _) =
  let thy = Why3.Env.read_theory env file thy in
  use task thy

let add_core_theories ~env tenv =
  let core_theories = [
    ((["int"], "Int"),
     [(CI_Int.p_int_opp, "prefix -");
      (CI_Int.p_int_add, "infix +" );
      (CI_Int.p_int_mul, "infix *" );
      (CI_Int.p_int_lt , "infix <" );
      (CI_Int.p_int_le , "infix <=")]);

    (* ((["int"], "EuclideanDivision"), *)
    (*  [(CI_Int.p_int_edivz, "div")]); *)

    ((["real"], "Real"),
     [(CI_Real.p_real0,    "zero");
      (CI_Real.p_real1,    "one");
      (CI_Real.p_real_opp, "prefix -");
      (CI_Real.p_real_add, "infix +" );
      (CI_Real.p_real_inv, "inv"     );
      (CI_Real.p_real_mul, "infix *" );
      (CI_Real.p_real_lt , "infix <" );
      (CI_Real.p_real_le , "infix <=")]);

    ((["real"], "FromInt"),
     [(CI_Real.p_real_of_int, "from_int")]);

    ((["map"], "Map"),
     [(CI_Map.p_get, "get");
      (CI_Map.p_set, "set");
     ]);

    ((["map"], "Const"),
     [(CI_Map.p_cst, "const")]);
  ]
  in

  tenv.te_th <- List.fold_left (add_core_theory env) tenv.te_th core_theories;

  let add_core_func tbl ((file,thy), operators) =
    let theory = Why3.Env.read_theory env file thy in
    let namesp = theory.WTheory.th_export in
    List.iter (fun (p, name) ->
        Hp.add tbl p (WTheory.ns_find_ls namesp [name], theory))
      operators
  in
  List.iter (add_core_func tenv.te_known_w3) core_theories

let add_core_tys ~env tenv =
  let core_ty_theories = [
    ((["map"], "Map"),
     [(CI_Map.p_map, "map")]);
    ((["int"], "Int"),
     [(CI_Int.p_int, "int")]);
    ((["real"], "Real"),
     [(CI_Real.p_real, "real")]);
    ((["bool"], "Bool"),
     [(CI_Bool.p_bool, "bool")]);
    ((["map"], "Map"),
     [(CI_Distr.p_distr, "map")]);
  ]
  in

  tenv.te_th <- List.fold_left (add_core_theory env) tenv.te_th core_ty_theories;

  let add_core_ty tbl ((file,thy), tys) =
    let theory = Why3.Env.read_theory env file thy in
    let namesp = theory.WTheory.th_export in
    List.iter (fun (p, name) ->
        Hp.add tbl p (WTheory.ns_find_ts namesp [name]))
      tys
  in
  List.iter (add_core_ty tenv.te_ty) core_ty_theories;
  tenv.te_th <- use tenv.te_th (Tuples.theory 0);
  Hp.add tenv.te_ty CI_Unit.p_unit (WTy.ts_tuple 0);
  Hp.add tenv.te_ty CI_Distr.p_distr (tenv.ts_distr)

let add_equal_symbole tenv =
    let mk_eq (t1, t2) =
      match t1.WTerm.t_ty with
      | None -> WTerm.t_iff (Cast.force_prop t1) (Cast.force_prop t2)
      | Some ty ->
        if   WTy.ty_equal ty WTy.ty_bool
        then WTerm.t_iff (Cast.force_prop t1) (Cast.force_prop t2)
        else WTerm.t_equ t1 t2 in

    let w3o_eq = {
      w3op_fo = `Internal (fun args _ -> mk_eq (as_seq2 args));
      w3op_ta = (fun tys -> let ty = Some (as_seq1 tys) in [], [ty;ty], None);
      w3op_ho = `HO_TODO ("eq", WTerm.ps_equ.WTerm.ls_args, None);
    }
    in Hp.add tenv.te_op CI_Bool.p_eq w3o_eq

let kwk ~env tenv =
  let core_match_theories = [
    ((["int"], "EuclideanDivision"),
     [(KProj (KApp (CI_Int.p_int_edivz, [KHole; KHole]), 0), "div");
      (KProj (KApp (CI_Int.p_int_edivz, [KHole; KHole]), 1), "mod")])
  ]
  in

  tenv.te_th <- List.fold_left (add_core_theory env) tenv.te_th core_match_theories;

  let add_kwk (file,thy) (k,name) =
    let theory = Why3.Env.read_theory env file thy in
    let namesp = theory.WTheory.th_export in
    (k, (WTheory.ns_find_ls namesp [name], theory))
  in
  List.rev (List.flatten
              (List.map
                 (fun (wth, syms) -> List.map (add_kwk wth) syms)
                 core_match_theories))

(* -------------------------------------------------------------------- *)

let init ~env hyps concl =
  let eenv   = LDecl.toenv hyps in

  let ts_mem = WTy.create_tysymbol (WIdent.id_fresh "memory") [] WTy.NoDef in
  let vta = WTy.create_tvsymbol (WIdent.id_fresh "ta") in
  let ta  = WTy.ty_var vta in
  let ts_distr = WTy.create_tysymbol (WIdent.id_fresh "distr") [vta] WTy.NoDef in

  let fs_mu  =
    WTerm.create_fsymbol (WIdent.id_fresh "mu")
      [WTy.ty_app ts_distr [ta]; WTy.ty_func ta WTy.ty_bool]
      WTy.ty_real
  in

  let distr_theory =
    let th = WTheory.create_theory (WIdent.id_fresh "Distr") in
    let th = WTheory.use_export th WTheory.bool_theory in
    let th = WTheory.use_export th WTheory.highord_theory in
    let th = WTheory.add_ty_decl th ts_distr in
    let th = WTheory.add_param_decl th fs_mu in
    WTheory.close_theory th
  in

  let fs_witness = WTerm.create_fsymbol (WIdent.id_fresh "witness") [] ta in
  let witness_theory =
    let th = WTheory.create_theory (WIdent.id_fresh "Witness") in
    let th = WTheory.add_param_decl th fs_witness in
    WTheory.close_theory th
  in

  let ec_theory = WTheory.create_theory (WIdent.id_fresh "EC_theory") in
  let tenv  = empty_tenv eenv ec_theory ts_mem ts_distr fs_witness fs_mu in

  add_core_theories ~env tenv;
  add_core_tys ~env tenv;
  add_core_ops tenv;
  add_equal_symbole tenv;

  tenv.tk_known_w3 <- kwk ~env tenv;

  tenv.te_th <- WTheory.add_ty_decl tenv.te_th tenv.ts_mem;
  tenv.te_th <- WTheory.use_export tenv.te_th distr_theory;
  tenv.te_th <- WTheory.use_export tenv.te_th witness_theory;

  let known = tenv.te_known_w3 in
  Hp.add known CI_Unit.p_tt (WTerm.fs_tuple 0, WTheory.tuple_theory 0);
  let mu = (fs_mu,distr_theory) in
  Hp.add known CI_Distr.p_mu mu;
  let witness = (fs_witness, witness_theory) in
  Hp.add known CI_Witness.p_witness witness;

  let init_select _ ax = ax.ax_visibility = `Visible in
  let toadd = EcEnv.Ax.all ~check:init_select eenv in
  List.iter (trans_axiom tenv) toadd;

  let hyps = LDecl.tohyps hyps in
  let lenv = lenv_of_hyps tenv hyps in

  let wterm = Cast.force_prop (trans_form (tenv, lenv) concl) in
  let pr = WDecl.create_prsymbol (WIdent.id_fresh "goal") in
  let dec = WDecl.create_prop_decl WDecl.Pgoal pr wterm in
  let ec_theory = WTheory.add_decl tenv.te_th dec in
  let ec_theory = WTheory.close_theory ec_theory in

  let task = WTask.split_theory ec_theory None None in
  List.hd task

(*---------------------------------------------------------------------------------*)
(* What follows is inspired from Frama-C                                           *)
(*---------------------------------------------------------------------------------*)

type prover_call = {
  prover : Why3.Whyconf.prover ;
  call : Why3.Call_provers.prover_call ;
  steps : int option ;
  timeout : float ;
  mutable timeover : float option ;
  mutable interrupted : bool ;
}

type verdict =
  | NoResult
  | Invalid
  | Unknown
  | Timeout
  | Stepout
  | Valid
  | Failed
  | Canceled

type result = {
  verdict : verdict ;
  cached : bool ;
  solver_time : float ;
  prover_time : float ;
  prover_steps : int ;
  prover_errpos : Lexing.position option ;
  prover_errmsg : string ;
}

let result ?(cached=false) ?(solver=0.0) ?(time=0.0) ?(steps=0) verdict =
  {
    verdict ;
    cached = cached ;
    solver_time = solver ;
    prover_time = time ;
    prover_steps = steps ;
    prover_errpos = None ;
    prover_errmsg = "" ;
  }

let no_result = result NoResult
let valid = result Valid
let invalid = result Invalid
let unknown = result Unknown
let timeout t = result ~time:t Timeout
let stepout n = result ~steps:n Stepout
let failed ?pos msg = {
  verdict = Failed ;
  cached = false ;
  solver_time = 0.0 ;
  prover_time = 0.0 ;
  prover_steps = 0 ;
  prover_errpos = pos ;
  prover_errmsg = msg ;
}
let canceled = result Canceled

let is_valid = function { verdict = Valid } -> true | _ -> false

let ping_prover_call ~config p =
  let pr = Why3.Call_provers.wait_on_call p.call in
  let r =
    match pr.pr_answer with
    | Timeout -> timeout pr.pr_time
    | Valid -> result ~time:pr.pr_time ~steps:pr.pr_steps Valid
    | Invalid -> result ~time:pr.pr_time ~steps:pr.pr_steps Invalid
    | OutOfMemory -> failed "out of memory"
    | StepLimitExceeded -> result ?steps:p.steps Stepout
    | Unknown _ -> unknown
    | _ when p.interrupted -> timeout p.timeout
    | Failure s -> failed s
    | HighFailure -> failed "Unknown error"
  in
  Some r

let call_prover_task ~timeout ~steps ~config prover call =
  let timeout = match timeout with None -> 0.0 | Some tlimit -> tlimit in
  let pcall = {
    call ; prover ;
    interrupted = false ;
    steps ; timeout ; timeover = None ;
  }
  in
  ping_prover_call ~config pcall

let run_batch pconf driver ~config ?script ~timeout ~steplimit prover task =
  let config = Why3.Whyconf.get_main config in
  let steps = match steplimit with Some 0 -> None | _ -> steplimit in
  let limit =
    let memlimit = Why3.Whyconf.memlimit config in
    let def = Why3.Call_provers.empty_limit in
    { Why3.Call_provers.limit_time = Why3.Opt.get_def def.limit_time timeout;
      Why3.Call_provers.limit_steps = Why3.Opt.get_def def.limit_steps steps;
      Why3.Call_provers.limit_mem = memlimit;
    }
  in
  let with_steps = match steps, pconf.Why3.Whyconf.command_steps with
    | None, _ -> false
    | Some _, Some _ -> true
    | Some _, None -> false
  in
  let steps = if with_steps then steps else None in
  let command = Why3.Whyconf.get_complete_command pconf ~with_steps in
  let inplace = if script <> None then Some true else None in
  let call =
    Why3.Driver.prove_task_prepared ?old:script ?inplace
      ~command ~limit ~config driver task
  in
  call_prover_task ~config ~timeout ~steps prover call

let pp_to_file f pp =
  let cout = open_out f in
  let fout = Format.formatter_of_out_channel cout in
  try
    pp fout ;
    Format.pp_print_flush fout () ;
    close_out cout
  with err ->
    Format.pp_print_flush fout () ;
    close_out cout ;
    raise err

let make_output_dir dir =
  if Sys.file_exists dir then ()
  else Unix.mkdir dir 0o770 ;

type mode =
  | Check (* Check scripts *)
  | Edit  (* Edit then check scripts *)
  | Fix   (* Try to check script, then edit script on non-success *)

let editor_command pconf config =
  try
    let ed = Why3.Whyconf.editor_by_id config pconf.Why3.Whyconf.editor in
    String.concat " " (ed.editor_command :: ed.editor_options)
  with Not_found ->
    Why3.Whyconf.(default_editor (get_main config))

let scriptfile ~(loc:EcLocation.t) ~name ~ext =
  let file = loc.loc_fname in
  let path = Filename.dirname file in
  let path = path ^ "/.interactive" in
  make_output_dir path;
  let name =
    if String.is_empty name then
      begin
        let name = Filename.basename file in
        let name = Filename.remove_extension name in
        let l,r = loc.loc_start in
        let sid = string_of_int l ^ string_of_int r in
        name ^ sid
      end
    else name
  in
  Format.sprintf "%s/%s%s" path name ext

let safe_remove f = try Unix.unlink f with Unix.Unix_error _ -> ()

let updatescript ~script driver task =
  let backup = script ^ ".bak" in
  Sys.rename script backup ;
  let old = open_in backup in
  pp_to_file script
    (fun fmt ->
       ignore @@ Why3.Driver.print_task_prepared ~old driver fmt task
    );
  close_in old ;
  let d_old = Digest.file backup in
  let d_new = Digest.file script in
  if String.equal d_new d_old then safe_remove backup

let editor ~script ~merge ~config pconf driver task =
  if merge then updatescript ~script driver task ;
  let command = editor_command pconf config in
  let config = Why3.Whyconf.get_main config in
  let call =
    Why3.Call_provers.call_editor
      ~command ~config script
  in
  call_prover_task ~config ~timeout:None ~steps:None pconf.prover call

let prepare ~name ~loc driver task =
  let ext = Filename.extension (Why3.Driver.file_of_task driver "S" "T" task) in
  let script = scriptfile ~loc ~name ~ext in
  if Sys.file_exists script then (script, true) else
    begin
      pp_to_file script
        (fun fmt ->
           ignore @@ Why3.Driver.print_task_prepared driver fmt task
        );
      (script, false)
    end

let interactive ~notify ~name ~coqmode ~loc pconf ~config driver prover task =
  let time = 10 in
  let timeout = if time <= 0 then None else Some (float time) in
  let script, merge =  prepare ~name ~loc driver task in
  if merge then updatescript ~script driver task ;
  match coqmode with
  | Check ->
    run_batch ~script ~timeout ~config pconf driver ~steplimit:None prover task
  | Edit ->
    editor ~script ~merge ~config pconf driver task |> obind (fun _ ->
        run_batch ~script ~timeout ~config pconf driver ~steplimit:None prover task)
  | Fix ->
    run_batch ~script ~timeout ~config pconf driver ~steplimit:None prover task
    |> obind (fun r ->
        if is_valid r then Some r else
          editor ~script ~merge ~config pconf driver task |> obind (fun _ ->
              run_batch ~script ~timeout ~config pconf driver ~steplimit:None prover task))

let is_trivial (t : Why3.Task.task) =
  let goal = Why3.Task.task_goal_fmla t in
  Why3.Term.t_equal goal Why3.Term.t_true

exception CoqNotFound

let cfg = lazy (Why3.Whyconf.init_config None)

let config () = Lazy.force cfg

let build_proof_task ~notify ~name ~coqmode ~loc ~config ~env task =
  try
    let (prover,pconf) =
      let fp = Why3.Whyconf.parse_filter_prover "Coq" in
      let provers = Why3.Whyconf.filter_provers config fp in
      begin
        match Why3.Whyconf.Mprover.is_empty provers with
        | false ->
          begin
            print_string "Versions of Coq found:\n";
            Why3.Whyconf.(Mprover.iter (fun k _ ->
                let s = Format.sprintf " %s\n" k.prover_version in
                print_string s;
              )) provers;

            let prover = Why3.Whyconf.Mprover.max_binding provers in
            let s = Format.sprintf "Take Coq %s\n" (fst prover).prover_version in
            print_string s;
            prover
          end
        | true -> raise CoqNotFound
      end
    in

    let drv = Why3.Driver.load_driver_for_prover (Why3.Whyconf.get_main config)
        env pconf
    in
    let task = Why3.Driver.prepare_task drv task in

    if is_trivial task then
      Some valid
    else
      interactive ~notify ~name ~coqmode ~loc pconf ~config drv prover task
  with
  | CoqNotFound ->
    notify |> oiter (fun notify -> notify `Critical (lazy (
        Format.asprintf "Prover Coq not installed or not configured@"
      )));
    None
  | exn ->
    notify |> oiter (fun notify -> notify `Critical (lazy (
        Format.asprintf "[Why3 Error] %a" Why3.Exn_printer.exn_printer exn
      )));
    None

let check ~loc ~name ?notify ?(coqmode=Edit) (hyps : LDecl.hyps) (concl : form) =
  let config = config () in
  let main_conf = Why3.Whyconf.get_main config in
  let ld = Why3.Whyconf.loadpath main_conf in
  let env = Why3.Env.create_env ld in
  let task = init ~env hyps concl in

  (* let s = Format.asprintf "%a\n" Why3.Pretty.print_task task in *)
  (* print_string s; *)

  match build_proof_task ~notify ~name ~coqmode ~loc ~config ~env task with
  | None -> false
  | Some r -> match r.verdict with
    | Valid -> true
    | _ -> false
