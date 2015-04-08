(* -------------------------------------------------------------------- *)
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

(* -------------------------------------------------------------------- *)
module WIdent  = Why3.Ident
module WTerm   = Why3.Term
module WTy     = Why3.Ty
module WTheory = Why3.Theory
module WDecl   = Why3.Decl
module WTask   = Why3.Task

(* -------------------------------------------------------------------- *)
let w_t_let vs w1 w2 =
   WTerm.t_let_simp w1 (WTerm.t_close_bound vs w2)

let w_t_lets vs ws w2 =
  List.fold_right2 w_t_let vs ws w2

(* -------------------------------------------------------------------- *)
type w3_known_op = WTerm.lsymbol * WTheory.theory

type w3ty = WTy.tysymbol

type w3op_ho =
  [ `HO_DONE of WTerm.lsymbol
  | `HO_TODO of string * WTy.ty list * WTy.ty option ]

type w3op = {
  (*---*) w3op_fo : w3op_fo;
  (*---*) w3op_ta : WTy.ty list -> WTy.ty option list * WTy.ty option;
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
type tenv = {
  (*---*) te_env        : EcEnv.env;
  mutable te_task       : WTask.task;
  (*---*) te_known_w3   : w3_known_op Hp.t;
  (*---*) te_ty         : w3ty Hp.t;
  (*---*) te_op         : w3op Hp.t;
  (*---*) te_lc         : w3op Hid.t;
  mutable te_lam        : WTerm.term Mta.t;
  (*---*) te_gen        : WTerm.term Hf.t;
  (*---*) te_proj       : WTerm.lsymbol Hdint.t;
  (*---*) te_xpath      : WTerm.lsymbol Hx.t; (* proc and var *)
  (*---*) te_absmod     : w3absmod Hid.t;     (* abstract module *)
}

let empty_tenv env task known =
  { te_env        = env;
    te_task       = task;
    te_known_w3   = known;
    te_ty         = Hp.create 0;
    te_op         = Hp.create 0; 
    te_lc         = Hid.create 0; 
    te_lam        = Mta.empty;
    te_gen        = Hf.create 0;
    te_proj       = Hdint.create 0;
    te_xpath      = Hx.create 0;
    te_absmod     = Hid.create 0;
  }

(* -------------------------------------------------------------------- *)
type lenv = {
  le_lv : WTerm.vsymbol Mid.t;
  le_tv : WTy.ty Mid.t;
}

let empty_lenv : lenv =
  { le_tv = Mid.empty; le_lv = Mid.empty; }

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

  let merge w1 w2 =
    if w1.WTerm.t_ty = None then w1, force_prop w2
    else if w2.WTerm.t_ty = None then prop_of_bool w1, w2
    else w1, w2

  let merges lw = 
    if List.exists (fun (_,w) -> is_none w.WTerm.t_ty) lw then
      List.map (fun (p,w) -> p, force_prop w) lw
    else lw
    
    
end

(* -------------------------------------------------------------------- *)
let load_wtheory genv th = 
  genv.te_task <- WTask.use_export genv.te_task th

let load_wtuple genv n = 
  let th = WTheory.tuple_theory n in
  load_wtheory genv th

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
    let ts = WTy.create_tysymbol (preid id) [] None in
    genv.te_task <- WTask.add_ty_decl genv.te_task ts;
    { env with le_tv = Mid.add id (WTy.ty_app ts []) env.le_tv }, ts
  in
    List.map_fold trans_tv empty_lenv ts

(* -------------------------------------------------------------------- *)
let instantiate tparams targs tres tys =
  let mtv = 
    List.fold_left2
      (fun mtv tv ty -> WTy.Mtv.add tv ty mtv) 
      WTy.Mtv.empty tparams tys in
  let targs = List.map (some |- WTy.ty_inst mtv) targs in
  let tres  = tres |> omap (WTy.ty_inst mtv) in
  (targs, tres)

(* -------------------------------------------------------------------- *)
let plain_w3op ?(name = "x") tparams ls = {
  w3op_fo = `LDecl ls;
  w3op_ta = instantiate tparams ls.WTerm.ls_args ls.WTerm.ls_value;
  w3op_ho = `HO_TODO (name, ls.WTerm.ls_args, ls.WTerm.ls_value);
}

let prop_w3op ?(name = "x") arity mkfo =
  let dom  = List.make arity None in
  let hdom = List.make arity WTy.ty_bool in

  { w3op_fo = `Internal mkfo;
    w3op_ta = (fun _ -> dom, None);
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
let ts_mem = WTy.create_tysymbol (WIdent.id_fresh "memory") [] None
let ty_mem = WTy.ty_app ts_mem [] 

let ts_distr, fs_mu, distr_theory =
  let th  = WTheory.create_theory (WIdent.id_fresh "Distr") in
  let th  = WTheory.use_export th WTheory.bool_theory in
  let th  = WTheory.use_export th WTheory.highord_theory in
  let vta = WTy.create_tvsymbol (WIdent.id_fresh "ta") in
  let ta  = WTy.ty_var vta in
  let tdistr = WTy.create_tysymbol (WIdent.id_fresh "distr") [vta] None in
  let th  = WTheory.add_ty_decl th tdistr in
  let mu  =
    WTerm.create_fsymbol (WIdent.id_fresh "mu")
      [WTy.ty_app tdistr [ta]; WTy.ty_func ta WTy.ty_bool]
      WTy.ty_real in
  let th = WTheory.add_param_decl th mu in
  tdistr, mu, WTheory.close_theory th

let ty_distr t = WTy.ty_app ts_distr [t]

let ty_mem_distr = ty_distr ty_mem

(* -------------------------------------------------------------------- *)
let mk_tglob genv mp = 
  assert (mp.EcPath.m_args = []);
  let id = EcPath.mget_ident mp in 
  match Hid.find_opt genv.te_absmod id with
  | Some { w3am_ty } -> w3am_ty
  | None ->
    (* create the type symbol *)
    let pid = preid id in
    let ts = WTy.create_tysymbol pid [] None in
    genv.te_task <- WTask.add_ty_decl genv.te_task ts;
    let ty = WTy.ty_app ts [] in
    Hid.add genv.te_absmod id { w3am_ty = ty };
    ty

(* -------------------------------------------------------------------- *)
let rec trans_ty ((genv, lenv) as env) ty =
  match ty.ty_node with
  | Tglob   mp -> 
    trans_tglob env mp
  | Tunivar _ -> assert false
  | Tvar    x -> trans_tv lenv x

  | Ttuple  ts-> 
      load_wtuple genv (List.length ts);
      WTy.ty_tuple (trans_tys env ts)

  | Tconstr (p, tys) ->
      let id = trans_pty genv p in
      WTy.ty_app id (trans_tys env tys)

  | Tfun (t1, t2) ->
      WTy.ty_func (trans_ty env t1) (trans_ty env t2)

and trans_tglob ((genv, _lenv) as env) mp = 
  let ty = NormMp.norm_tglob genv.te_env mp in
  match ty.ty_node with
  | Tglob mp -> mk_tglob genv mp
 
  | _ -> trans_ty env ty
  
and trans_tys env tys = List.map (trans_ty env) tys

and trans_pty genv p =
  match Hp.find_opt genv.te_ty p with
  | Some tv -> tv
  | None    -> trans_tydecl genv (p, EcEnv.Ty.by_path p genv.te_env)

and trans_tydecl genv (p, tydecl) =
  let pid = preid_p p in
  let lenv, tparams = lenv_of_tparams tydecl.tyd_params in

  let ts, opts, decl =
    match tydecl.tyd_type with
    | `Abstract _ ->
        let ts = WTy.create_tysymbol pid tparams None in
        (ts, [], WDecl.create_ty_decl ts)

    | `Concrete ty ->
        let ty = trans_ty (genv, lenv) ty in
        let ts = WTy.create_tysymbol pid tparams (Some ty) in
        (ts, [], WDecl.create_ty_decl ts)

    | `Datatype dt ->
        let ncs  = List.length dt.tydt_ctors in
        let ts   = WTy.create_tysymbol pid tparams None in

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
        let ts = WTy.create_tysymbol pid tparams None in

        Hp.add genv.te_ty p ts;

        let wdom  = tconstr p (List.map (tvar |- fst) tydecl.tyd_params) in
        let wdom  = trans_ty (genv, lenv) wdom in

        let for_field (fname, fty) =
          let wfid  = pqoname (prefix p) fname in
          let wfty  = trans_ty (genv, lenv) fty in
          let wcls  = WTerm.create_lsymbol (preid_p wfid) [wdom] (Some wfty) in
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

  genv.te_task <- WTask.add_decl genv.te_task decl;
  Hp.add genv.te_ty p ts;
  List.iter (fun (p, wop) -> Hp.add genv.te_op p wop) opts;
  ts

(* -------------------------------------------------------------------- *)
let rm_mp_args mp = 
  EcPath.mpath mp.EcPath.m_top []

let rm_xp_args xp = 
  let mp = rm_mp_args xp.EcPath.x_top in
  EcPath.xpath mp xp.EcPath.x_sub

(* -------------------------------------------------------------------- *)
let trans_binding genv lenv (x, xty) =
  let wty = 
    match xty with
    | GTty ty -> trans_ty (genv, lenv) ty
    | GTmem _ -> ty_mem
    | _ -> assert false in
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
let mk_highorder_func ids dom codom mk =
  let pid = WIdent.id_fresh (ids ^ "_ho") in
  let ty = List.fold_right WTy.ty_func dom (odfl WTy.ty_bool codom) in
  let ls' = WTerm.create_fsymbol pid [] ty in
  let decl' = WDecl.create_param_decl ls' in
  let pid_spec = WIdent.id_fresh (ids ^ "_ho_spec") in
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
      let ls, decl, decl_s = mk_highorder_func id dom codom (w3op_fo wop) in
      genv.te_task <- WTask.add_decl genv.te_task decl;
      genv.te_task <- WTask.add_decl genv.te_task decl_s;
      wop.w3op_ho <- `HO_DONE ls; ls

(* -------------------------------------------------------------------- *)
let cast_arg a ty =
  match a.WTerm.t_ty, ty with
  | None  , None   -> a
  | None  , Some _ -> Cast.force_bool a
  | Some _, None   -> Cast.force_prop a
  | Some _, Some _ -> a

let cast_app mk args targs tres = mk (List.map2 cast_arg args targs) tres

let rec highorder_type targs tres =
  match targs with
  | [] -> odfl WTy.ty_bool tres
  | a::targs -> WTy.ty_func (odfl WTy.ty_bool a) (highorder_type targs tres)

let apply_highorder f args =
  List.fold_left (fun f a -> WTerm.t_func_app f (Cast.force_bool a)) f args

let apply_wop genv wop tys args =
  let (targs, tres) = wop.w3op_ta tys in
  let arity = List.length targs in
  let nargs = List.length args in
  
  if nargs = arity then cast_app (w3op_fo wop) args targs tres
  else if nargs < arity then
    let fty = highorder_type targs tres in
    let ls' = w3op_ho_lsymbol genv wop in
    apply_highorder (WTerm.fs_app ls' [] fty) args 
  else (* arity < nargs : too many arguments *) 
    let args1,args2 = List.takedrop arity args in
    apply_highorder (cast_app (w3op_fo wop) args1 targs tres) args2

(* -------------------------------------------------------------------- *)   
let trans_lambda genv wvs wbody = 
  try Mta.find (wvs,wbody) genv.te_lam 
    with Not_found ->
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
      let lam_sym = WIdent.id_fresh "unamed_lambda" in 
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
      let spec_sym = 
        WDecl.create_prsymbol (WIdent.id_fresh "unamed_lambda_spec") in
      let decl_spec = WDecl.create_prop_decl WDecl.Paxiom spec_sym spec in
      genv.te_task <- WTask.add_decl genv.te_task decl_sym;
      genv.te_task <- WTask.add_decl genv.te_task decl_spec;
      genv.te_lam  <- Mta.add (wvs,wbody) flam_app genv.te_lam;
      flam_app
 
(* -------------------------------------------------------------------- *)
let rec trans_form ((genv, lenv) as env : tenv * lenv) (fp : form) =
  match fp.f_node with
  | Fquant (qt, bds, body) ->
      let lenv, wbds = trans_bindings genv lenv bds in
      let wbody = trans_form (genv,lenv) body in
      (match qt with
      | Lforall -> WTerm.t_forall_close wbds [] (Cast.force_prop wbody)
      | Lexists -> WTerm.t_exists_close wbds [] (Cast.force_prop wbody)
      | Llambda -> trans_lambda genv wbds wbody)
      
  | Fint n ->
      let n = BI.to_string n in
      let n = Why3.Number.ConstInt (Why3.Number.int_const_dec n) in
      WTerm.t_const n
      
  | Fif    _ -> trans_app env fp []
  | Flet   _ -> trans_app env fp []
  | Flocal _ -> trans_app env fp []
  | Fop    _ -> trans_app env fp []

    (* Special case for `%r` *)
  | Fapp({ f_node = Fop (p, [])},  [{f_node = Fint n}]) 
      when p_equal p CI_Real.p_real_of_int ->
    let n = BI.to_string n in
    let n = Why3.Number.ConstReal (Why3.Number.real_const_dec n "" None) in
    WTerm.t_const n
      
  | Fapp (f, args) ->
      trans_app env f (List.map (trans_form env) args)
    
  | Ftuple args -> 
      let args = List.map (trans_form_b env) args in
      load_wtuple genv (List.length args);
      WTerm.t_tuple args
      
  | Fproj (tfp, i) ->
      let wtfp = trans_form env tfp in
      let wty  = oget (wtfp.WTerm.t_ty) in
      let n    = 
        match wty.WTy.ty_node with
        | WTy.Tyapp (_, targs) -> List.length targs
        | _ -> assert false

      in WTerm.t_app_infer (trans_proj genv (n, i)) [wtfp]
      
  | Fpvar(pv,mem) -> trans_pvar env pv fp.f_ty mem 

  | Fglob (m,mem) -> trans_glob env m mem

  | Fpr pr        -> trans_pr env pr
  | FeagerF _ 
  | FhoareF   _ | FhoareS   _
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
      let wt, wf = Cast.merge wt wf in
      WTerm.t_if_simp (Cast.force_prop wb) wt wf 
      
  | Fapp (f, args') ->
      let args' = List.map (trans_form env) args' in
      trans_app env f (args'@args)
      
  | _ -> 
      apply_highorder (trans_form env f) args

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
      let lenv, vs = trans_binding genv lenv (id,GTty ty) in
      let w2 = trans_app (genv,lenv) f2 args in
      w_t_let vs w1 w2

  | LTuple ids -> 
      let ids  = List.map (snd_map gtty) ids in
      let nids = List.length ids in
      let lenv, vs = trans_bindings genv lenv ids in
      load_wtuple genv nids;
      let pat =
        WTerm.pat_app (WTerm.fs_tuple nids)
          (List.map WTerm.pat_var vs) (WTerm.t_type w1) in
      let w2 = trans_app (genv, lenv) f2 args in
      let br = WTerm.t_close_branch pat w2 in
      WTerm.t_case w1 [br]

  | LRecord _ -> assert false

(* -------------------------------------------------------------------- *)
and trans_op (genv:tenv) p =
  try Hp.find genv.te_op p with Not_found -> create_op ~body:true genv p

(* -------------------------------------------------------------------- *)
and trans_proj genv (n, i) =
  try  Hdint.find genv.te_proj (n, i)
  with Not_found -> create_proj genv (n, i)

(* -------------------------------------------------------------------- *)
and trans_pvar ((genv, _) as env) pv ty mem = 
  let pv = NormMp.norm_pvar genv.te_env pv in
  let xp = 
    if   is_loc pv
    then pv.pv_name 
    else rm_xp_args pv.pv_name in 

  let ls = 
    match Hx.find_opt genv.te_xpath xp with
    | Some ls -> ls
    | None -> 
        let ty = Some (trans_ty env ty) in
        let pid = preid_xp xp in
        let ls = WTerm.create_lsymbol pid [ty_mem] ty in
        genv.te_task <- WTask.add_param_decl genv.te_task ls;
        Hx.add genv.te_xpath xp ls; ls

  in WTerm.t_app_infer ls [trans_mem env mem]

(* -------------------------------------------------------------------- *)
and trans_glob ((genv, _) as env) mp mem = 
  let f = NormMp.norm_glob genv.te_env mem mp in
  match f.f_node with
  | Fglob (mp, mem) ->
      assert (mp.EcPath.m_args = []);

      let id   = EcPath.mget_ident mp in 
      let wmem = trans_mem env mem in 
      let w3op = 
        match Hid.find_opt genv.te_lc id with
        | Some w3op -> w3op
        | None -> 
          let ty  = Some (mk_tglob genv mp) in
          let pid = preid id in
          let ls  = WTerm.create_lsymbol pid [ty_mem] ty in
          let w3op = 
            { w3op_fo = `LDecl ls;
              w3op_ta = (fun _tys -> [Some ty_mem], ty);
              w3op_ho = `HO_TODO (EcIdent.name id, [ty_mem], ty); } in
          genv.te_task <- WTask.add_param_decl genv.te_task ls;
          Hid.add genv.te_lc id w3op;
          w3op
      in apply_wop genv w3op [] [wmem]

  | _ -> trans_form env f

(* -------------------------------------------------------------------- *)
and trans_mem (genv,lenv) mem =  
  match Hid.find_opt genv.te_lc mem with
  | Some w3op -> apply_wop genv w3op [] []
  | None -> WTerm.t_var (oget (Mid.find_opt mem lenv.le_lv))

(* -------------------------------------------------------------------- *)
and trans_pr ((genv,lenv) as env) {pr_mem; pr_fun; pr_args; pr_event} = 
  let wmem = trans_mem env pr_mem in 
  let warg = trans_form_b env pr_args in

  (* Translate the procedure *)
  let xp = NormMp.norm_xfun genv.te_env pr_fun in
  let ls =
    let trans () =
      let tya = oget warg.WTerm.t_ty in
      let tyr = Some ty_mem_distr in
      let pid = preid_xp xp in
      let ls  = WTerm.create_lsymbol pid [tya; ty_mem] tyr in
      genv.te_task <- WTask.add_param_decl genv.te_task ls;
      Hx.add genv.te_xpath xp ls;
      ls
    in Hx.find_opt genv.te_xpath xp |> ofdfl trans
  in

  let d = WTerm.t_app ls [warg; wmem] (Some ty_mem_distr) in
  let wev = 
    let lenv, wbd = trans_binding genv lenv (mhr, GTmem None) in
    let wbody = trans_form_b (genv,lenv) pr_event in
    trans_lambda genv [wbd] wbody

  in WTerm.t_app_infer fs_mu [d; wev]
  
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

    genv.te_task <- WTask.add_param_decl genv.te_task lsym;
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
  let body = cast_arg body wcodom in 
  let body = 
    match wcodom, body.WTerm.t_ty with
    | None  , Some _ -> Cast.force_prop body
    | Some _, None   -> Cast.force_bool body
    | _, _ -> body

  in (params, body)

(* -------------------------------------------------------------------- *)
and trans_fix (genv, lenv) o =
  let (lenv, vs) = trans_lvars genv lenv o.opf_args in
  let pterm   = List.map (List.nth vs) (fst o.opf_struct) in
  let ptermty = List.map (fun x -> x.WTerm.vs_ty) pterm in
  let ptermc  = List.length ptermty in

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
          
          let we = trans_form (genv, lenv) fe in

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
            then WTerm.pat_app (WTerm.fs_tuple ptermc) ptn (WTy.ty_tuple ptermty)
            else oget (List.ohead ptn)
          in (ptn, we) :: ptns

    in compile [] ([], o.opf_branches)
  in

  let ptns = Cast.merges ptns in
  let ptns =
    List.rev_map
      (fun (p, e) -> WTerm.t_close_branch p e)
      ptns in

  let mtch =
    if   ptermc > 1
    then WTerm.t_tuple (List.map WTerm.t_var pterm)
    else WTerm.t_var (oget (List.ohead pterm)) in

  let body = WTerm.t_case mtch ptns in

  (vs, body)

(* -------------------------------------------------------------------- *)
and create_op ?(body = false) (genv : tenv) p =
  let op = EcEnv.Op.by_path p genv.te_env in
  let lenv, wparams = lenv_of_tparams op.op_tparams in
  let dom, codom = EcEnv.Ty.signature genv.te_env op.op_ty in

  let wdom   = trans_tys (genv, lenv) dom in
  let wcodom =
    if   ER.EqTest.is_bool genv.te_env codom
    then None
    else Some (trans_ty (genv, lenv) codom) in

  let known, ls =
    match Hp.find_opt genv.te_known_w3 p with
    | Some (ls, th) ->
        (load_wtheory genv th; (true, ls))

    | None ->
        let ls = WTerm.create_lsymbol (preid_p p) wdom wcodom in
        (false, ls)
  in

  let w3op =
    let name = ls.WTerm.ls_name.WIdent.id_string in
    { w3op_fo = `LDecl ls;
      w3op_ta = instantiate wparams ls.WTerm.ls_args ls.WTerm.ls_value;
      w3op_ho = `HO_TODO (name, wdom, wcodom); }
  in

  let register = OneShot.mk (fun () -> Hp.add genv.te_op p w3op) in

  if not known then begin
    let decl =
      match body, op.op_kind with
      | true, OB_oper (Some (OP_Plain body)) ->
          let body = EcFol.form_of_expr EcFol.mhr body in
          let wparams, wbody = trans_body (genv, lenv) wdom wcodom body in
          WDecl.create_logic_decl [WDecl.make_ls_defn ls wparams wbody]

      | true, OB_oper (Some (OP_Fix body)) ->
        OneShot.now register;
        let wparams, wbody = trans_fix (genv, lenv) body in
        let wbody = cast_arg wbody ls.WTerm.ls_value in
        WDecl.create_logic_decl [WDecl.make_ls_defn ls wparams wbody]
   
      | true, OB_pred (Some body) ->
          let wparams, wbody = trans_body (genv, lenv) wdom None body in
          WDecl.create_logic_decl [WDecl.make_ls_defn ls wparams wbody]
        
      | _, _ -> WDecl.create_param_decl ls

    in
      OneShot.now register;
      genv.te_task <- WTask.add_decl genv.te_task decl
  end;

  w3op

(* -------------------------------------------------------------------- *)
and create_proj genv (n, i) =
  let tvs  = Array.init n (fun _ -> WTy.create_tvsymbol (WIdent.id_fresh "a")) in
  let ts   = Array.map WTy.ty_var tvs in
  let tt   = WTy.ty_tuple (Array.to_list ts) in
  let ti   = ts.(i) in
  let vi   = WTerm.create_vsymbol (WIdent.id_fresh "v") ti in
  let pat  = Array.map WTerm.pat_wild ts in
  let pat  = pat.(i) <- WTerm.pat_var vi; Array.to_list pat in
  let br   = WTerm.pat_app (WTerm.fs_tuple n) pat tt in
  let br   = WTerm.t_close_branch br (WTerm.t_var vi) in
  let va   = WTerm.create_vsymbol (WIdent.id_fresh "x") tt in
  let body = WTerm.t_case (WTerm.t_var va) [br] in
  let s    = Format.sprintf "proj%i_%i" n i in
  let ls   = WTerm.create_lsymbol (WIdent.id_fresh s) [tt] (Some ti) in
  let decl = WDecl.create_logic_decl [WDecl.make_ls_defn ls [va] body] in

  Hdint.add genv.te_proj (n, i) ls;
  genv.te_task <- WTask.add_decl genv.te_task decl;
  ls

(* -------------------------------------------------------------------- *)
let add_axiom ((genv, _) as env) preid form = 
  let w    = trans_form env form in
  let pr   = WDecl.create_prsymbol preid in
  let decl = WDecl.create_prop_decl WDecl.Paxiom pr (Cast.force_prop w) in
  genv.te_task <- WTask.add_decl genv.te_task decl

(* -------------------------------------------------------------------- *)
let trans_hyp ((genv, _) as env) (x, ty) =
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
      w3op_ta = (fun _ -> (List.map some wdom, wcodom));
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
      genv.te_task <- WTask.add_decl genv.te_task decl;
      Hid.add genv.te_lc x w3op

  | LD_hyp f -> 
      (* FIXME: Selection of hypothesis *)
      add_axiom env (preid x) f

  | LD_mem    _ -> 
      let wcodom = Some ty_mem in
      let ls =  WTerm.create_lsymbol (preid x) [] wcodom in
      let w3op = {
        w3op_fo = `LDecl ls;
        w3op_ta = (fun _ -> ([], wcodom));
        w3op_ho = `HO_TODO (EcIdent.name x, [], wcodom);
      } in
        
      genv.te_task <- WTask.add_param_decl genv.te_task ls;
      Hid.add genv.te_lc x w3op

  | LD_modty  _ -> ()

  | LD_abs_st _ -> ()

(* -------------------------------------------------------------------- *)
let lenv_of_hyps genv (hyps : hyps) : lenv =
  let lenv = fst (lenv_of_tparams_for_hyp genv hyps.h_tvar) in
  List.iter (trans_hyp (genv, lenv)) (List.rev hyps.h_local); lenv

(* -------------------------------------------------------------------- *)
let trans_axiom genv (p, ax) = 
  match ax.ax_spec with
  | Some f when not ax.ax_nosmt ->
      let lenv = fst (lenv_of_tparams ax.ax_tparams) in    
      add_axiom (genv, lenv) (preid_p p) f
  | _ -> ()

(* -------------------------------------------------------------------- *)
let mk_pred1 f l _ = f (as_seq1 l)
let mk_pred2 f l _ = curry f (as_seq2 l)

let mk_true  = fun _ _ -> WTerm.t_true
let mk_false = fun _ _ -> WTerm.t_false
let mk_not   = mk_pred1 WTerm.t_not
let mk_anda  = mk_pred2 WTerm.t_and_asym
let mk_and   = mk_pred2 WTerm.t_and
let mk_ora   = mk_pred2 WTerm.t_or_asym
let mk_or    = mk_pred2 WTerm.t_or
let mk_imp   = mk_pred2 WTerm.t_implies
let mk_iff   = mk_pred2 WTerm.t_iff

let core_types = [
  (CI_Unit.p_unit, WTy.ts_tuple 0);
  (CI_Bool.p_bool, WTy.ts_bool);
  (CI_Int .p_int , WTy.ts_int);
  (CI_Real.p_real, WTy.ts_real);
  (CI_Distr.p_distr, ts_distr);
]

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

let core_theories = [
  ((["int"], "Int"),
     [(CI_Int.p_int_opp, "prefix -");
      (CI_Int.p_int_add, "infix +" );
      (CI_Int.p_int_sub, "infix -" );
      (CI_Int.p_int_mul, "infix *" );
      (CI_Int.p_int_lt , "infix <" );  
      (CI_Int.p_int_le , "infix <=");  
      (CI_Int.p_int_gt , "infix >" );  
      (CI_Int.p_int_ge , "infix >=")]);

  ((["real"], "Real"),
     [(CI_Real.p_real_opp, "prefix -");
      (CI_Real.p_real_add, "infix +" );
      (CI_Real.p_real_sub, "infix -" );
      (CI_Real.p_real_mul, "inv"     );
      (CI_Real.p_real_mul, "infix *" );
      (CI_Real.p_real_lt , "infix <" );  
      (CI_Real.p_real_le , "infix <=");  
      (CI_Real.p_real_gt , "infix >" );  
      (CI_Real.p_real_ge , "infix >=")]);

  ((["real"], "FromInt"),
     [(CI_Real.p_real_of_int, "from_int")]);
]

let core_theories = Lazy.from_fun (fun () ->
  let add_core_theory tbl (thname, operators) =
    let theory = curry EcProvers.get_w3_th thname in
    let namesp = theory.WTheory.th_export in
    List.iter (fun (p, name) ->
      Hp.add tbl p (WTheory.ns_find_ls namesp [name], theory))
      operators
  in
  let tbl = Hp.create 0 in
  Hp.add tbl CI_Unit.p_tt (WTerm.fs_tuple 0, WTheory.tuple_theory 0);
  List.iter (add_core_theory tbl) core_theories; 
  Hp.add tbl CI_Distr.p_mu (fs_mu, distr_theory);
  tbl)

(* -------------------------------------------------------------------- *)
let add_core_bindings (env : tenv) =
  (* Core types *)
  List.iter (curry (Hp.add env.te_ty)) core_types;

  (* Core operators *)
  List.iter (fun (p, id, arity, fo) ->
    Hp.add env.te_op p (prop_w3op ~name:id arity fo))
    core_ops;

  (* Add symbol for equality *)
  begin
    let mk_eq (t1, t2) =
      match t1.WTerm.t_ty with
      | None -> WTerm.t_iff (Cast.force_prop t1) (Cast.force_prop t2) 
      | Some ty ->
        if   WTy.ty_equal ty WTy.ty_bool
        then WTerm.t_iff (Cast.force_prop t1) (Cast.force_prop t2) 
        else WTerm.t_equ t1 t2 in

    let w3o_eq = {
      w3op_fo = `Internal (fun args _ -> mk_eq (as_seq2 args));
      w3op_ta = (fun tys -> let ty = Some (as_seq1 tys) in [ty;ty], None);
      w3op_ho = `HO_TODO ("eq", WTerm.ps_equ.WTerm.ls_args, None);
    }

    in Hp.add env.te_op CI_Bool.p_eq w3o_eq
  end;
  (* Add modules stuff *)
  env.te_task <- WTask.add_ty_decl env.te_task ts_mem

(* -------------------------------------------------------------------- *)
(* See "Lightweight Relevance Filtering for Machine-Generated           *)
(* Resolution Problems" for a description of axioms selection.          *)

type ax_info = {
  ax_name : path;
  ax_symb : Sp.t;
} 

module Frequency = struct

  (* -------------------------------------------------------------------- *)
  type relevant = Sp.t * Sx.t

  let r_union (sp1,sf1) (sp2,sf2) = Sp.union sp1 sp2, Sx.union sf1 sf2 
  let r_inter (sp1,sf1) (sp2,sf2) = Sp.inter sp1 sp2, Sx.inter sf1 sf2 
  let r_diff  (sp1,sf1) (sp2,sf2) = Sp.diff  sp1 sp2, Sx.diff sf1 sf2 
  let r_card  (sp ,sf )           = Sp.cardinal sp + Sx.cardinal sf

  type all_rel = [ `OP of path | `PROC of xpath]

  let r_fold g (sp,sf) a = 
    Sp.fold (fun p a -> g (`OP p) a) sp 
      (Sx.fold (fun f a -> g (`PROC f) a) sf a)

  (* -------------------------------------------------------------------- *)
  let f_ops unwanted_op f : relevant = 
    let sp = ref Sp.empty in
    let sf = ref Sx.empty in
    let rec doit f = 
      match f.f_node with
      | Fint _ | Flocal _ | Fpvar _ | Fglob _ -> ()
      | Fop (p,_) -> 
        if not (Sp.mem p unwanted_op) then sp := Sp.add p !sp
      | Fquant (_ , _ , f1) -> doit f1
      | Fif      (f1, f2, f3) -> doit f1;doit f2; doit f3
      | Flet     (_, f1, f2)  -> doit f1;doit f2
      | Fapp     (e, es)      -> List.iter doit (e :: es)
      | Ftuple   es           -> List.iter doit es
      | Fproj    (e, _)       -> doit e
        
      | FhoareF _ | FhoareS _ | FbdHoareF _ | FbdHoareS _ 
      | FequivF _ | FequivS _ | FeagerF _  -> ()
      | Fpr pr -> 
        sf := Sx.add pr.pr_fun !sf; 
        doit pr.pr_event; doit pr.pr_args in
    doit f;
    if not (Sx.is_empty !sf) then sp := Sp.add CI_Distr.p_mu !sp; 
    !sp, !sf

  
  let f_ops_hyp unwanted_op rs (_,ld) = 
    match ld with
    | LD_var(_ty, b) -> 
      begin match b with
      | None -> rs 
      | Some b ->  r_union rs (f_ops unwanted_op b)
      end
    | LD_hyp f       -> 
      r_union rs (f_ops unwanted_op f)
    | LD_mem _ | LD_modty _ | LD_abs_st _ -> 
      rs

  let f_ops_hyps unwanted_op = List.fold_left (f_ops_hyp unwanted_op)

  let f_ops_goal unwanted_op hyps concl = 
    f_ops_hyps unwanted_op (f_ops unwanted_op concl) hyps


  (* -------------------------------------------------------------------- *)
  type frequency = int Hp.t * int Hx.t

  let add unwanted_op ftabp ftabf ax = 
    let addp p = 
      if not (Sp.mem p unwanted_op) then
        let n = Hp.find_def ftabp 0 p in
        Hp.replace ftabp p (n+1) in
    let addx f = 
      let n = Hx.find_def ftabf 0 f in
      Hx.replace ftabf f (n+1);
      addp CI_Distr.p_mu in
    
    let rec add f =
      match f.f_node with
      | Fop      (p,_)        -> addp p
      | Fquant   (_ , _ , f1) -> add f1
      | Fif      (f1, f2, f3) -> add f1;add f2; add f3
      | Flet     (_, f1, f2)  -> add f1;add f2
      | Fapp     (e, es)      -> List.iter add (e :: es)
      | Ftuple   es           -> List.iter add es
      | Fproj    (e, _)       -> add e
      | Fpr      pr           -> addx pr.pr_fun;add pr.pr_event;add pr.pr_args
      | _ -> () in
    oiter add ax.ax_spec 
  
  let init unwanted_op all : frequency = 
    let ftabp = Hp.create 0 in
    let ftabf = Hx.create 0 in
    List.iter (fun (_,ax) -> add unwanted_op ftabp ftabf ax) all;
    ftabp, ftabf 

  let frequency (ftabp,ftabf) = function
    | `OP p   -> Hp.find_def ftabp 0 p
    | `PROC f -> Hx.find_def ftabf 0 f

end

type relevant_info = {
  ri_p : float;            
  ri_c : float;
  ri_wanted_ax   : Sp.t;         (* wanted axiom   *)
  ri_unwanted_ax : Sp.t;         (* unwanted axiom *)
  ri_unwanted_op : Sp.t;         (* do not take into account *)
  ri_max_axioms  : int;          (* maximun number of axioms  *)
}

let relevant_clause env ri rs = 
  (* [toadd] the initial list of axiom to be added *)
  if ri.ri_max_axioms <= Sp.cardinal ri.ri_wanted_ax then 
      Sp.fold 
        (fun path toadd -> (path, EcEnv.Ax.by_path path env) :: toadd)
        ri.ri_wanted_ax [] 

  else
    (* Initialisation *)
    (* [all] the list of all axioms, not unwanted and can be send to smt *)
    let init_select p ax = 
      not ax.ax_nosmt && not (Sp.mem p ri.ri_unwanted_ax) in
    let all = EcEnv.Ax.all ~check:init_select env in

    (* [ftab] frequency table number of occurency of operators *)
    let ftab = Frequency.init ri.ri_unwanted_op all in

    (* [other] the list of all axioms names and their set of used operators 
             (excepted unwanted operators). Do not include toadd. *)
    let toadd, other = 
      let add_ax (toadd, other as toot) (p, ax as pax) = 
        match ax.ax_spec with
        | None -> toot 
        | Some f -> 
          let used = Frequency.f_ops ri.ri_unwanted_op f in
          let paxu = pax, used in
          if Sp.mem p ri.ri_wanted_ax then paxu::toadd, other
          else toadd, paxu :: other in
      List.fold_left add_ax ([],[]) all in

    (* [symbols_of ax] return the set of operator used in ax *)
    let symbols_of (_,s) = s in
    let frequency_function freq = 1. +. log1p (float_of_int freq) in
    let update_rs toadd rs rel =
      List.fold_left (fun (toadd,rs) ax -> 
        (fst ax :: toadd, Frequency.r_union (symbols_of ax) rs)) (toadd,rs) rel in
      
    let clause_mark p rs other =
      let rel = ref [] in
      let newo = ref [] in
      let do1 ax = 
        let cs = symbols_of ax in
        let r  = Frequency.r_inter cs rs in
        let ir = Frequency.r_diff cs r in
        let weight path m = 
          let freq = Frequency.frequency ftab path in
          let w = frequency_function freq in
          m +. w in
        let m = Frequency.r_fold weight r 0. in
        let m = m /. (m +. float_of_int (Frequency.r_card ir)) in
        if p <= m then rel := ax :: !rel else newo := ax :: !newo in
      List.iter do1 other;
      !rel, !newo in
    
    let rec aux toadd rs p other = 
      if ri.ri_max_axioms <= List.length toadd then toadd
      else
        let rel, other = clause_mark p rs other  in
        if rel = [] then toadd 
        else
          let toadd, rs = update_rs toadd rs rel in
          let p = p +. (1. -. p) /. ri.ri_c in
          aux toadd rs p other in

(*    let rs = Sp.diff rs ri.ri_unwanted_op in *)
    let toadd, rs = update_rs [] rs toadd in
    aux toadd rs ri.ri_p other 
   
(*let select_add_axioms genv ri rs =
  let rs = Sp.diff rs ri.ri_unwanted_op in
  let toadd = EcSearch.search genv.te_env [`ByPath rs] in
  List.iter (trans_axiom genv) toadd  *)

let select_add_axioms genv ri rs =
  let toadd = relevant_clause genv.te_env ri rs in
  List.iter (trans_axiom genv) toadd 

(* -------------------------------------------------------------------- *)

let unwanted_ops = 
  Sp.of_list [
    CI_Unit.p_tt;

    CI_Bool.p_true;
    CI_Bool.p_false;

    CI_Bool.p_not;
    CI_Bool.p_anda;
    CI_Bool.p_and;
    CI_Bool.p_ora;
    CI_Bool.p_or;
    CI_Bool.p_imp;
    CI_Bool.p_iff;
    CI_Bool.p_eq;

    CI_Int.p_int_opp;
    CI_Int.p_int_add;
    CI_Int.p_int_sub;
    CI_Int.p_int_mul;
    CI_Int.p_int_le;
    CI_Int.p_int_lt;
    CI_Int.p_int_ge;
    CI_Int.p_int_gt;

    CI_Real.p_real_opp;
    CI_Real.p_real_add;
    CI_Real.p_real_sub;
    CI_Real.p_real_mul;
    CI_Real.p_real_inv;
    CI_Real.p_real_div;
    CI_Real.p_real_of_int;
    CI_Real.p_real_le;
    CI_Real.p_real_lt;
    CI_Real.p_real_ge;
    CI_Real.p_real_gt;
  ]

(* -------------------------------------------------------------------- *)
let check ?notify pi (hyps : LDecl.hyps) (concl : form) =
  (try Unix.unlink "task.why" with Unix.Unix_error _ -> ());
  let (tt, task) = EcUtils.timed (fun () ->
    let task  = (None : WTask.task) in
    let task  = WTask.use_export task WTheory.builtin_theory in
    let task  = WTask.use_export task (WTheory.tuple_theory 0) in
    let task  = WTask.use_export task WTheory.bool_theory in
    let task  = WTask.use_export task WTheory.highord_theory in
    let task  = WTask.use_export task distr_theory in
    let known = Lazy.force core_theories in
    let tenv  = empty_tenv (LDecl.toenv hyps) task known in
    let ()    = add_core_bindings tenv in
    let lenv  = lenv_of_hyps tenv (LDecl.tohyps hyps) in
    let wterm = trans_form (tenv, lenv) concl in
    let pr    = WDecl.create_prsymbol (WIdent.id_fresh "goal") in
    let decl  = WDecl.create_prop_decl WDecl.Pgoal pr wterm in
  (* Hypothesis selection *) 
    let rs =
      Frequency.f_ops_goal unwanted_ops (LDecl.tohyps hyps).h_local concl in
    let ri = {
      ri_p           = 0.6; 
      ri_c           = 2.4;
      ri_wanted_ax   = Sp.empty;
      ri_unwanted_ax = Sp.empty;
      ri_unwanted_op = unwanted_ops;
      ri_max_axioms  = pi.EcProvers.pr_max;
    } in
    select_add_axioms tenv ri rs;
    (* Add conclusion *)
    WTask.add_decl tenv.te_task decl) () in

(*  if 2 <= pi.EcProvers.pr_verbose then
    Printf.eprintf "[W]SMT translation: %f\n%!" tt; *)

  if 3 <= pi.EcProvers.pr_verbose || 
    EcUtils.is_some (Os.getenv "EC_SMT_DEBUG") then begin 
    let stream = open_out "task.why" in
    EcUtils.try_finally
      (fun () -> Format.fprintf
        (Format.formatter_of_out_channel stream)
        "%a@." Why3.Pretty.print_task task)
      (fun () -> close_out stream)
  end; 

  let (tp,res) = 
    EcUtils.timed (fun task -> 
       EcProvers.execute_task ?notify pi task = Some true) task in
(*  if 1 <= pi.EcProvers.pr_verbose then
    Printf.eprintf "[W]SMT proved: %f\n%!" tp;
  res *)
  
 
