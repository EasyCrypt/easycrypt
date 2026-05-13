(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcIdent
open EcPath
open EcAst
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
(* Why3-side representation of a TC class declaration. The dict record
   has one field per ancestor-class op (flattened, with cumulative chain
   renames applied at the leaf level — diamond uniqueness is enforced at
   class declaration, see [ecScope.ml:1985-1995]). The axioms predicate
   asserts all flat ancestor + own axioms over a dict-typed argument.

   See [[tc-smt-encoding-dict]] memory: encoding is dictionary-passing
   for soundness; every TC op application becomes a dict-field projection. *)
type w3_class_field = {
  wcf_name    : EcSymbols.symbol;   (* leaf-level (renamed) name *)
  wcf_origin  : EcPath.path;        (* class where this op was declared *)
  wcf_orig_name : EcSymbols.symbol; (* op name at its origin class *)
  wcf_proj    : WTerm.lsymbol;      (* why3 field projection *)
}

type w3_class_decl = {
  wcd_path        : EcPath.path;       (* the EC class path *)
  wcd_tparam      : WTy.tvsymbol;      (* the carrier tvar 'a *)
  wcd_ts          : WTy.tysymbol;      (* the dict record type symbol *)
  wcd_ctor        : WTerm.lsymbol;     (* the record constructor *)
  wcd_fields      : w3_class_field list; (* in record-order *)
  wcd_by_leaf     : (EcSymbols.symbol, w3_class_field) Hashtbl.t;
  wcd_axioms      : WTerm.lsymbol;     (* the axioms predicate symbol *)
}

(* -------------------------------------------------------------------- *)
type kpattern =
  | KHole
  | KApp  of EcPath.path * kpattern list
  | KProj of kpattern * int

(* -------------------------------------------------------------------- *)
type tenv = {
  (*---*) te_env        : EcEnv.env;
  mutable te_task       : WTask.task;
  (*---*) ty_known_w3   : w3_known_ty Hp.t;
  (*---*) te_known_w3   : w3_known_op Hp.t;
  (*---*) tk_known_w3   : (kpattern * w3_known_op) list;
  (*---*) te_ty         : w3ty Hp.t;
  (*---*) te_op         : w3op Hp.t;
  (*---*) te_lc         : w3op Hid.t;
  mutable te_lam        : WTerm.term Mta.t;
  (*---*) te_gen        : WTerm.term Hf.t;
  (*---*) te_xpath      : WTerm.lsymbol Hx.t;  (* proc and global var *)
  (*---*) te_absmod     : w3absmod Hid.t;      (* abstract module     *)
  (*---*) te_class      : w3_class_decl Hp.t;  (* TC class declarations *)
  (*---*) te_idict      : (WTerm.term * w3_class_decl) Hp.t;
    (* instance dicts, keyed by tcinstance path *)
  (*---*) te_absdict    : (EcPath.path * int, WTerm.term * w3_class_decl)
                          Hashtbl.t;
    (* declared-abstract-type dicts, keyed by (type path, bound offset).
       Abstract carriers are static (don't vary per goal/lemma), so
       these live at tenv level so they're visible to both goal
       translation AND lemma (trans_axiom) translation. *)
}

let empty_tenv env task (kwty, kw, kwk) =
  { te_env        = env;
    te_task       = task;
    te_known_w3   = kw;
    ty_known_w3   = kwty;
    tk_known_w3   = kwk;
    te_ty         = Hp.create 0;
    te_op         = Hp.create 0;
    te_lc         = Hid.create 0;
    te_lam        = Mta.empty;
    te_gen        = Hf.create 0;
    te_xpath      = Hx.create 0;
    te_absmod     = Hid.create 0;
    te_class      = Hp.create 0;
    te_idict      = Hp.create 0;
    te_absdict    = Hashtbl.create 17;
  }

(* -------------------------------------------------------------------- *)
(* Carrier key for an in-scope dict. [DKVar] keys tparam-ident carriers
   (true type parameters); [DKAbs] keys declared-abstract type-constructor
   carriers (path-based, e.g. section-introduced [declare type t]). *)
type dict_carrier =
  | DKVar of EcIdent.t
  | DKAbs of EcPath.path

(* Tparam dict bindings: for each [(carrier, offset)] referencing a TC
   bound on the goal's free type parameters, [le_tdict] stores the why3
   dict term and class decl. Populated by Phase C. *)
type lenv = {
  le_lv     : WTerm.vsymbol Mid.t;
  le_tv     : WTy.ty Mid.t;
  le_mt     : EcMemory.memtype Mid.t;
  le_tdict  : (dict_carrier * int * WTerm.term * w3_class_decl) list;
}

let empty_lenv : lenv =
  { le_tv = Mid.empty; le_lv = Mid.empty;
    le_mt = Mid.empty; le_tdict = []; }

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
let dump_tasks (tasks : WTask.task) (filename : string) =
  let stream = open_out filename in
    EcUtils.try_finally
      (fun () -> Format.fprintf
        (Format.formatter_of_out_channel stream)
        "%a@." Why3.Pretty.print_task tasks)
      (fun () -> close_out stream)

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
let load_wtheory (genv : tenv) (th : WTheory.theory) : unit =
  genv.te_task <- WTask.use_export genv.te_task th

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

let load_tuple genv n =
  load_wtheory genv (Tuples.theory n)

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
  let trans_tv env ((id, _) : ty_param) =
    let tv = WTy.create_tvsymbol (preid id) in
    { env with le_tv = Mid.add id (WTy.ty_var tv) env.le_tv }, tv
  in
    List.map_fold trans_tv empty_lenv ts

let lenv_of_tparams_for_hyp genv ts =
  let trans_tv env ((id, _) : ty_param) =
    let ts = WTy.create_tysymbol (preid id) [] WTy.NoDef in
    genv.te_task <- WTask.add_ty_decl genv.te_task ts;
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
  let targs = List.map (some -| WTy.ty_inst mtv) targs in
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
let ts_mem = WTy.create_tysymbol (WIdent.id_fresh "memory") [] WTy.NoDef
let ty_mem = WTy.ty_app ts_mem []

let ts_distr, fs_mu, distr_theory =
  let th  = WTheory.create_theory (WIdent.id_fresh "Distr") in
  let th  = WTheory.use_export th WTheory.bool_theory in
  let th  = WTheory.use_export th WTheory.highord_theory in
  let vta = WTy.create_tvsymbol (WIdent.id_fresh "ta") in
  let ta  = WTy.ty_var vta in
  let tdistr = WTy.create_tysymbol (WIdent.id_fresh "distr") [vta] WTy.NoDef in
  let th  = WTheory.add_ty_decl th tdistr in
  let mu  =
    WTerm.create_fsymbol (WIdent.id_fresh "mu")
      [WTy.ty_app tdistr [ta]; WTy.ty_func ta WTy.ty_bool]
      WTy.ty_real in
  let th = WTheory.add_param_decl th mu in
  tdistr, mu, WTheory.close_theory th

let ty_distr t = WTy.ty_app ts_distr [t]

(* -------------------------------------------------------------------- *)
let fs_witness, witness_theory =
  let th = WTheory.create_theory (WIdent.id_fresh "Witness") in
  let vta = WTy.create_tvsymbol (WIdent.id_fresh "ta") in
  let ta  = WTy.ty_var vta in
  let witness  =
    WTerm.create_fsymbol (WIdent.id_fresh "witness") [] ta in
  let th = WTheory.add_param_decl th witness in
  witness, WTheory.close_theory th

let w_witness ty =
  WTerm.fs_app fs_witness [] ty

(* -------------------------------------------------------------------- *)
let mk_tglob genv m =
  match Hid.find_opt genv.te_absmod m with
  | Some { w3am_ty } -> w3am_ty
  | None ->
    (* create the type symbol *)
    let pid = preid m in
    let ts = WTy.create_tysymbol pid [] WTy.NoDef in
    genv.te_task <- WTask.add_ty_decl genv.te_task ts;
    let ty = WTy.ty_app ts [] in
    Hid.add genv.te_absmod m { w3am_ty = ty };
    ty

(* -------------------------------------------------------------------- *)
let rec trans_ty ((genv, lenv) as env) ty =
  match ty.ty_node with
  | Tglob   mp ->
    mk_tglob genv mp
  | Tunivar _ -> assert false
  | Tvar    x -> trans_tv lenv x

  | Ttuple  ts-> wty_tuple genv (trans_tys env ts)

  | Tconstr (p, tys) ->
      let id = trans_pty genv p in
      WTy.ty_app id (trans_tys env (List.fst tys))

  | Tfun (t1, t2) ->
      WTy.ty_func (trans_ty env t1) (trans_ty env t2)

and trans_tys env tys = List.map (trans_ty env) tys

and trans_pty genv p =
  match Hp.find_opt genv.te_ty p with
  | Some tv -> tv
  | None    ->
    match Hp.find_opt genv.ty_known_w3 p with
    | Some (ts, th) ->
      load_wtheory genv th;
      Hp.add genv.te_ty p ts;
      ts
    | None -> trans_tydecl genv (p, EcEnv.Ty.by_path p genv.te_env)

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

        let wdom = tconstr_tc p (etyargs_of_tparams tydecl.tyd_params) in
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

        let wdom  = tconstr_tc p (etyargs_of_tparams tydecl.tyd_params) in
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

  genv.te_task <- WTask.add_decl genv.te_task decl;
  Hp.add genv.te_ty p ts;
  List.iter (fun (p, wop) -> Hp.add genv.te_op p wop) opts;
  ts

(* -------------------------------------------------------------------- *)
let trans_memtype ((genv, _) as env) mt =
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
let mk_highorder_symb ids dom codom =
  let pid = WIdent.id_fresh (ids ^ "_ho") in
  let ty = List.fold_right WTy.ty_func dom (odfl WTy.ty_bool codom) in
  WTerm.create_fsymbol pid [] ty, ty

let mk_highorder_func ids dom codom mk =
  let ls', ty = mk_highorder_symb ids dom codom in
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
  let eargs =
    List.map w_witness textra in
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
let kmatch =
  let module E = struct exception MFailure end in

  let rec doit (acc : form list) (k : kpattern) (f : form) =
    match k, fst_map f_node (destr_app f) with
    | KHole, _ ->
        f :: acc

    | KProj (sk, i), (Fproj (sf, j), []) when i = j ->
        doit acc sk sf

    | KApp (sp, ks), (Fop (p, _), fs)
        when EcPath.p_equal sp p && List.length ks = List.length fs
      -> List.fold_left2 doit acc ks fs

    | _, _ -> raise E.MFailure
  in

  fun k f -> try Some (List.rev (doit [] k f)) with E.MFailure -> None

(* -------------------------------------------------------------------- *)
(* Forward reference for the lazy instance-dict emitter. Defined later
   (after [trans_class] and [add_axiom], which it depends on); the
   mutual-recursion block of [trans_form] / [try_dict_proj] uses it
   through this reference to break the cycle. *)
let emit_instance_dict_ref
  : (tenv -> EcPath.path -> (WTerm.term * w3_class_decl) option) ref
  = ref (fun _ _ -> None)

(* -------------------------------------------------------------------- *)
(* Walk [tc]'s parent chain via the [lift] indices, composing renamings
   as we go. Returns the ancestor reached and the cumulative renaming
   from the ancestor's op names to [tc]'s op names. *)
let walk_lift
  (env : EcEnv.env) (tc : EcAst.typeclass) (lift : int list)
  : EcAst.typeclass * (EcSymbols.symbol * EcSymbols.symbol) list
=
  List.fold_left (fun (tc, ren) i ->
    let decl = EcEnv.TypeClass.by_path tc.EcAst.tc_name env in
    let subst =
      List.fold_left2
        (fun s (a, _) etyarg -> Mid.add a etyarg s)
        Mid.empty decl.tc_tparams tc.tc_args in
    let (parent, _lbl, p_ren) = List.nth decl.tc_prts i in
    let parent = EcCoreSubst.Tvar.subst_tc subst parent in
    let ren' = EcTypeClass.compose_renaming ~outer:p_ren ~inner:ren in
    (parent, ren')
  ) (tc, []) lift

(* -------------------------------------------------------------------- *)
let rec trans_kpattern env (k, (ls, wth)) f =
  match kmatch k f with None -> raise CanNotTranslate | Some args ->

  load_wtheory (fst env) wth;

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

  let wargs = List.map (trans_form env) args in

  apply_wop (fst env) w3op [] wargs

(* -------------------------------------------------------------------- *)
and trans_kpatterns env (ks : (kpattern * w3_known_op) list) (f : form) =
  EcUtils.oget ~exn:CanNotTranslate
    (List.Exceptionless.find_map
       (fun k -> try Some (trans_kpattern env k f) with CanNotTranslate -> None)
       ks)

(* -------------------------------------------------------------------- *)
and trans_form ((genv, lenv) as env : tenv * lenv) (fp : form) =
  try trans_kpatterns env genv.tk_known_w3 fp with CanNotTranslate ->

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
  | Fint n ->
      WTerm.t_int_const (BI.to_why3 n)

  | Fif    _ -> trans_app env fp []
  | Fmatch _ -> trans_app env fp []
  | Flet   _ -> trans_app env fp []
  | Flocal _ -> trans_app env fp []
  | Fop    _ -> trans_app env fp []

    (* Special case for `%r` *)
  | Fapp({ f_node = Fop (p, [])},  [{f_node = Fint n}])
      when p_equal p CI_Real.p_real_of_int ->
    WTerm.t_real_const (BI.to_why3 n)

  | Fapp (f,args) -> trans_app env f (List.map (trans_form env) args)

  | Ftuple args   -> wt_tuple genv (List.map (trans_form_b env) args)

  | Fproj (tfp,i) -> wproj_tuple genv (trans_form env tfp) i

  | Fpvar(pv,mem) -> trans_pvar env pv fp.f_ty mem

  | Fglob (m,mem) -> trans_glob env m mem

  | Fpr pr        -> trans_pr env pr

  | FeagerF _
  | FhoareF  _  | FhoareS   _
  | FeHoareF   _ | FeHoareS   _
  | FbdHoareF _ | FbdHoareS _
  | FequivF   _ | FequivS   _
    -> trans_gen env fp

and trans_form_b env f = Cast.force_bool (trans_form env f)

(* -------------------------------------------------------------------- *)
(* Phase D — if [Fop (p, ts)] is a TC class op AND a dict for its
   carrier-witness is in scope (a tparam dict in [lenv.le_tdict] or an
   instance dict in [genv.te_idict]), emit a record-field projection
   rather than an opaque uninterpreted symbol. Returning [None] falls
   back to the legacy translation (e.g. for ops with no in-scope dict
   yet — those should be rare once Phases B/C are wired in). *)
and try_dict_proj
    ((genv, lenv) : tenv * lenv)
    (p : EcPath.path)
    (etyargs : EcAst.etyarg list)
    (args : WTerm.term list)
  : WTerm.term option
=
  let open EcDecl in
  let op = EcEnv.Op.by_path p genv.te_env in
  match op.op_kind with
  | OB_oper (Some (OP_TC (class_path, local_name))) -> begin
    (* The class op's etyargs end with a phantom "self" entry carrying
       the witness for the class constraint. *)
    match List.rev etyargs with
    | (_, [witness]) :: _ -> begin
        let try_finish (dict_term : WTerm.term) (w3cd : w3_class_decl)
                       (lift : int list) : WTerm.term option =
          let self_decl =
            EcEnv.TypeClass.by_path w3cd.wcd_path genv.te_env in
          let self_tc =
            { EcAst.tc_name = w3cd.wcd_path;
              tc_args =
                EcDecl.etyargs_of_tparams self_decl.EcDecl.tc_tparams; } in
          let (anc_arrived, ren) = walk_lift genv.te_env self_tc lift in
          if not (EcPath.p_equal anc_arrived.EcAst.tc_name class_path) then
            None
          else
            let leaf_name =
              try List.assoc local_name ren
              with Not_found -> local_name in
            match Hashtbl.find_opt w3cd.wcd_by_leaf leaf_name with
            | None -> None
            | Some field ->
              (* HO projection: [proj_ls : dict -> field_ty]. Apply to
                 dict, then use [apply_highorder] for args (which uses
                 why3's [@] for function-typed values). Works for full,
                 partial, AND over-application uniformly. *)
              let fv = WTerm.t_app_infer field.wcf_proj [dict_term] in
              Some (apply_highorder fv args)
        in
        let find_dict (key : dict_carrier) (offset : int) =
          List.find_opt
            (fun (k, off', _, _) ->
              offset = off' &&
              (match k, key with
               | DKVar a, DKVar b -> EcIdent.id_equal a b
               | DKAbs a, DKAbs b -> EcPath.p_equal a b
               | _ -> false))
            lenv.le_tdict in
        match witness with
        | EcAst.TCIAbstract { support = `Var x; offset; lift } -> begin
            match find_dict (DKVar x) offset with
            | None -> None
            | Some (_, _, dict_term, w3cd) ->
              try_finish dict_term w3cd lift
          end
        | EcAst.TCIAbstract { support = `Abs t; offset; lift } -> begin
            (* [te_absdict] is the tenv-level table for declared-abstract
               carriers: tenv-level so trans_axiom / trans_body (op body
               translation) can ALSO project through it, even though
               they build their own [lenv]s. *)
            match Hashtbl.find_opt genv.te_absdict (t, offset) with
            | None -> None
            | Some (dict_term, w3cd) ->
              try_finish dict_term w3cd lift
          end
        | EcAst.TCIConcrete { path; lift; _ } -> begin
            match !emit_instance_dict_ref genv path with
            | None -> None
            | Some (dict_term, w3cd) ->
              try_finish dict_term w3cd lift
          end
        | _ -> None
      end
    | _ -> None
    end
  | _ -> None

(* -------------------------------------------------------------------- *)
and trans_app  ((genv, lenv) as env : tenv * lenv) (f : form) args =
  match f.f_node with
  | Fquant (Llambda, bds, body) ->
      trans_fun env bds body args

  | Fop (p, ts) -> begin
      match try_dict_proj env p ts args with
      | Some w -> w
      | None ->
          let wop = trans_op genv p in
          let ts  = List.fst ts in
          let tys = List.map (trans_ty (genv,lenv)) ts in
          apply_wop genv wop tys args
    end

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
  let wcty = trans_ty (genv, lenv) (tconstr_tc p tvs) in
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
and trans_op (genv:tenv) p =
  try Hp.find genv.te_op p with Not_found -> create_op ~body:true genv p

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
        let ls = WTerm.create_lsymbol pid [ty_mem] ty in
        genv.te_task <- WTask.add_param_decl genv.te_task ls;
        Hx.add genv.te_xpath xp ls; ls
    in
    WTerm.t_app_infer ls [m]

(* -------------------------------------------------------------------- *)
and trans_glob ((genv, _) as env) m mem =
  let wmem = trans_mem env ~forglobal:true mem in
  let w3op =
    match Hid.find_opt genv.te_lc m with
    | Some w3op -> w3op
    | None ->
       let ty  = Some (mk_tglob genv m) in
       let pid = preid m in
       let ls  = WTerm.create_lsymbol pid [ty_mem] ty in
       let w3op =
         { w3op_fo = `LDecl ls;
           w3op_ta = (fun _tys -> [], [Some ty_mem], ty);
           w3op_ho = `HO_TODO (EcIdent.name m, [ty_mem], ty); } in
       genv.te_task <- WTask.add_param_decl genv.te_task ls;
       Hid.add genv.te_lc m w3op;
       w3op
  in apply_wop genv w3op [] [wmem]

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
  let _, mt = EcEnv.Fun.prF_memenv (EcIdent.create "&dummy") pr_fun genv.te_env in
  let mty = trans_memtype env mt in
  let tyr = ty_distr mty in
  let ls =
    let trans () =
      let tya = oget warg.WTerm.t_ty in
      let tyr = Some tyr in
      let pid = preid_xp xp in
      let ls  = WTerm.create_lsymbol pid [tya; ty_mem] tyr in
      genv.te_task <- WTask.add_param_decl genv.te_task ls;
      Hx.add genv.te_xpath xp ls;
      ls
    in Hx.find_opt genv.te_xpath xp |> ofdfl trans
  in

  let d = WTerm.t_app ls [warg; wmem] (Some tyr) in

  let wev =
    let lenv, wbd = trans_binding genv lenv (pr_event.m, GTmem mt) in
    let wbody = trans_form_b (genv,lenv) pr_event.inv in
    trans_lambda genv [wbd] wbody

  in WTerm.t_app_infer fs_mu [d; wev]

(* -------------------------------------------------------------------- *)
and trans_gen ((genv, lenv) as env :  tenv * lenv) (fp : form) =
  match Hf.find_opt genv.te_gen fp with
  | None ->
    let name = WIdent.id_fresh "x" in
    let argsty, args =
      let fv = Mid.keys fp.f_fv in
      let fv = List.pmap (fun x -> Mid.find_opt x lenv.le_lv) fv in
      (
        List.map (fun v -> v.WTerm.vs_ty) fv,
        List.map WTerm.t_var fv
      ) in

    let wty  =
      if   EcReduction.EqTest.is_bool genv.te_env fp.f_ty
      then None
      else Some (trans_ty env fp.f_ty) in

    let lsym = WTerm.create_lsymbol name argsty wty in
    let term = WTerm.t_app_infer lsym args in

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
          let fe = EcCoreFol.form_of_expr e in

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
and create_op ?(body = false) (genv : tenv) p =
  let op = EcEnv.Op.by_path p genv.te_env in
  let lenv, wparams = lenv_of_tparams op.op_tparams in
  let dom, codom = EcEnv.Ty.signature genv.te_env op.op_ty in
  let textra =
    List.filter (fun (tv, _) -> not (Mid.mem tv (EcTypes.Tvar.fv op.op_ty))) op.op_tparams in
  let textra =
    List.map (fun (tv, _) -> trans_ty (genv,lenv) (tvar tv)) textra in
  let wdom   = trans_tys (genv, lenv) dom in
  let wcodom =
    if   ER.EqTest.is_bool genv.te_env codom
    then None
    else Some (trans_ty (genv, lenv) codom) in

  (* FIXME: this is a ack for constructor, when the constructor is
   * translated before its type. Should the same be done for some
   * other kinds of operators, like projections? *)
  try Hp.find genv.te_op p with Not_found ->

  let known, ls =
    match Hp.find_opt genv.te_known_w3 p with
    | Some (ls, th) ->
      load_wtheory genv th; (true, ls)

    | None ->
        let ls = WTerm.create_lsymbol (preid_p p) (textra@wdom) wcodom in
        (false, ls)
  in

  let w3op =
    let name = ls.WTerm.ls_name.WIdent.id_string in
    let w3op_ho =
      if EcDecl.is_fix op then
        let ls, decl, decl_s =
          mk_highorder_func name (textra@wdom) wcodom (WTerm.t_app ls)
        in
          `HO_FIX (ls, decl, decl_s, ref false)
      else
        `HO_TODO (name, textra@wdom, wcodom) in

    { w3op_fo = `LDecl ls;
      w3op_ta = instantiate wparams ~textra wdom wcodom;
      w3op_ho = w3op_ho; }
  in

  let register = OneShot.mk (fun () -> Hp.add genv.te_op p w3op) in

  if not known then begin
    let wextra = List.map (fun ty ->
                     WTerm.create_vsymbol (WIdent.id_fresh "_") ty) textra in
    let decl =
      let default () = WDecl.create_param_decl ls in

      if op.op_opaque.smt then
        default ()
      else
        match body, op.op_kind with
        | true, OB_oper (Some (OP_Plain body)) ->
            let wparams, wbody = trans_body (genv, lenv) wdom wcodom body in
            WDecl.create_logic_decl [WDecl.make_ls_defn ls (wextra@wparams) wbody]

        | true, OB_oper (Some (OP_Fix body)) ->
          OneShot.now register;
          let wparams, wbody = trans_fix (genv, lenv) (wdom, body) in
          let wbody = Cast.arg wbody ls.WTerm.ls_value in
          WDecl.create_logic_decl [WDecl.make_ls_defn ls (wextra@wparams) wbody]

        | true, OB_pred (Some (PR_Plain body)) ->
            let wparams, wbody = trans_body (genv, lenv) wdom None body in
            WDecl.create_logic_decl [WDecl.make_ls_defn ls (wextra@wparams) wbody]

        | _, _ ->
            default ()

    in
      OneShot.now register;

      match w3op.w3op_ho with
      | `HO_FIX (ls, ho_decl, ho_decl_s, r) -> begin
          if !r then begin
            List.iter
              (fun d -> genv.te_task <- WTask.add_decl genv.te_task d)
              [ho_decl; decl; ho_decl_s];
            w3op.w3op_ho <- `HO_DONE ls
          end else begin
            genv.te_task <- WTask.add_decl genv.te_task decl;
            w3op.w3op_ho <-
              let name = ls.WTerm.ls_name.WIdent.id_string in
              `HO_TODO (name, textra@wdom, wcodom)
          end
        end
      | _ ->
          genv.te_task <- WTask.add_decl genv.te_task decl
  end;

  w3op

(* -------------------------------------------------------------------- *)
(* Phase A — lazy emission of a TC class declaration as a why3 record
   type (the dict) + a predicate symbol asserting the class axioms.

   With auto-import disabled and renames being abbreviations only, the
   dict record carries one field per visible ancestor op AT THE LEAF
   CLASS, named by the cumulative chain rename (diamond uniqueness is
   guaranteed by [ecScope.ml]'s collision check at class declaration).
   Each TC op application Fop(class_op, [.. witness ..]) will translate
   in Phase D as a projection of the matching field of the dict the
   witness identifies.                                                  *)
let trans_class (genv : tenv) (cp : EcPath.path) : w3_class_decl =
  try Hp.find genv.te_class cp with Not_found ->

  let class_decl = EcEnv.TypeClass.by_path cp genv.te_env in
  (* Self-typeclass at our own tparams; ancestors_with_renaming uses
     this to expand the chain with proper substitution. *)
  let self_tc =
    { EcAst.tc_name = cp;
      tc_args = EcDecl.etyargs_of_tparams class_decl.EcDecl.tc_tparams; } in

  (* Walk ancestors with cumulative rename (leaf -> ancestor). Each
     pair (anc, ren) gives an ancestor typeclass and a list of
     [(ancestor_op_name, leaf_local_name)] entries. Empty ren = no
     renaming along this path. *)
  let chain =
    EcTypeClass.ancestors_with_renaming genv.te_env self_tc in

  (* Fresh tvar 'a for the dict's carrier. We use the basename of [cp]
     as the type-symbol name. *)
  let alpha_tv = WTy.create_tvsymbol (WIdent.id_fresh "a") in
  let alpha_ty = WTy.ty_var alpha_tv in
  let dict_pid = preid_p cp in
  let dict_ts =
    WTy.create_tysymbol dict_pid [alpha_tv] WTy.NoDef in
  let dict_ty = WTy.ty_app dict_ts [alpha_ty] in

  (* For each (ancestor, cumulative_rename) collect the ancestor's
     [tc_ops], producing fields named by [lookup_ren ren op_name].
     Dedup by leaf-level name: same canonical-origin op reached
     through multiple chain paths produces one field. *)
  let lookup_ren ren n =
    match List.assoc_opt n ren with Some n' -> n' | None -> n in
  let by_name = ref EcMaps.Mstr.empty in
  let ordered = ref [] in
  let anc_prefix_of anc =
    EcPath.prefix anc.EcAst.tc_name in
  List.iter (fun (anc, ren) ->
    let anc_decl =
      EcEnv.TypeClass.by_path anc.EcAst.tc_name genv.te_env in
    let anc_prefix = anc_prefix_of anc in
    List.iter (fun (op_id, _raw_op_ty) ->
      let orig_name = EcIdent.name op_id in
      let leaf_name = lookup_ren ren orig_name in
      if not (EcMaps.Mstr.mem leaf_name !by_name) then begin
        (* Look up the BOUND class op (xpath in the theory): its
           [op_tparams]/[op_ty] are the env-bound versions, where the
           class's implicit carrier has been replaced by a fresh
           [Tvar self_id] (see [ecEnv.ml:912]). Use that to translate
           the field's type, substituting [self_id] to our dict's
           [alpha_id]. *)
        let bound_path = EcPath.pqoname anc_prefix orig_name in
        match EcEnv.Op.by_path_opt bound_path genv.te_env with
        | None -> ()  (* shouldn't happen for a class op *)
        | Some bound_op ->
        match List.rev bound_op.EcDecl.op_tparams with
        | [] -> ()  (* class op without self tparam — shouldn't happen *)
        | (self_id, _) :: _ ->
        let lenv =
          { empty_lenv with le_tv = Mid.add self_id alpha_ty Mid.empty } in
        (* Higher-order projection [proj_ls : dict -> field_ty]. The
           field's type may be a function (e.g. mop : 'a -> 'a -> 'a);
           applications then use why3's [@] operator. This is the only
           shape that handles ALL of full, partial, and over-application
           consistently without lambdas — partial uses become bare
           [proj_ls dict] (an function-typed value), which Alt-Ergo
           can pass around as a closure. *)
        let wty = trans_ty (genv, lenv) bound_op.EcDecl.op_ty in
        let proj_id =
          let safe =
            String.map (fun c ->
              if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
                 || (c >= '0' && c <= '9') || c = '_'
              then c else '_'
            ) leaf_name in
          WIdent.id_fresh (Printf.sprintf "fld_%s" safe) in
        let proj_ls =
          WTerm.create_lsymbol proj_id [dict_ty] (Some wty) in
        let field = {
          wcf_name      = leaf_name;
          wcf_origin    = anc.EcAst.tc_name;
          wcf_orig_name = orig_name;
          wcf_proj      = proj_ls;
        } in
        by_name := EcMaps.Mstr.add leaf_name field !by_name;
        ordered := field :: !ordered
      end
    ) anc_decl.EcDecl.tc_ops
  ) chain;
  let fields = List.rev !ordered in

  (* Emit the dict type as OPAQUE (no constructor) and each field
     projection as a regular first-order function symbol. Avoiding
     why3's data-decl machinery keeps the SMT-LIB output flat — no
     ADT pattern matching, no inductive elimination, no [@]-based
     higher-order applications for function-typed fields. *)
  genv.te_task <- WTask.add_ty_decl genv.te_task dict_ts;
  List.iter (fun f ->
    genv.te_task <- WTask.add_param_decl genv.te_task f.wcf_proj
  ) fields;
  (* A nominal constructor lsymbol — kept in [w3cd.wcd_ctor] for
     compatibility but NOT emitted into the task. *)
  let ctor_id = WIdent.id_fresh (EcPath.basename cp ^ "_mk") in
  let ctor_ls =
    WTerm.create_lsymbol ctor_id [] (Some dict_ty) in

  (* Axioms predicate symbol — body is filled in by Phase A.3.
     For now: uninterpreted parameter declaration. *)
  let axioms_pid = WIdent.id_fresh (EcPath.basename cp ^ "_axioms") in
  let axioms_ls =
    WTerm.create_psymbol axioms_pid [dict_ty] in
  let axioms_decl = WDecl.create_param_decl axioms_ls in
  genv.te_task <- WTask.add_decl genv.te_task axioms_decl;

  let by_leaf = Hashtbl.create 17 in
  List.iter (fun f -> Hashtbl.replace by_leaf f.wcf_name f) fields;

  let w3cd = {
    wcd_path     = cp;
    wcd_tparam   = alpha_tv;
    wcd_ts       = dict_ts;
    wcd_ctor     = ctor_ls;
    wcd_fields   = fields;
    wcd_by_leaf  = by_leaf;
    wcd_axioms   = axioms_ls;
  } in
  Hp.add genv.te_class cp w3cd;
  w3cd

(* -------------------------------------------------------------------- *)
let add_axiom ((genv, _) as env) preid form =
  let w    = trans_form env form in
  let pr   = WDecl.create_prsymbol preid in
  let decl = WDecl.create_prop_decl WDecl.Paxiom pr (Cast.force_prop w) in
  genv.te_task <- WTask.add_decl genv.te_task decl

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
    genv.te_task <- WTask.add_decl genv.te_task decl;
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

      genv.te_task <- WTask.add_param_decl genv.te_task ls;
      Hid.add genv.te_lc x w3op;
      (genv, lenv)

  | LD_modty  _ -> env

  | LD_abs_st _ -> env

(* -------------------------------------------------------------------- *)
(* For polymorphic axioms over a TC bound, dict-pass: introduce a fresh
   dict binder per (tparam_id, offset, class) bound, register it in
   [le_tdict], wrap the body in [forall ds. <class>_axioms 'a d_i ->
   <body>], and translate. The premise matches any registered
   instance's axioms-hold (Phase B), letting SMT instantiate at the
   carrier. The body's class-op Fops translate through Phase D's
   projection over the bound dict.

   In the why3 task this looks like:
     axiom name : forall ('a : ty) (d : C_dict 'a),
       C_axioms 'a d -> <body using d's projections>
*)
let trans_axiom genv (p, ax) =
  let lenv, _wparams = lenv_of_tparams ax.ax_tparams in
  (* Collect (tparam_id, offset, class, tparam_ty) entries for each TC
     bound on each tparam. *)
  let tc_binders =
    List.concat_map (fun (tparam_id, tcs) ->
      let tparam_ty =
        try Mid.find tparam_id lenv.le_tv
        with Not_found -> assert false in
      List.mapi (fun offset tc ->
        (tparam_id, offset, tc, tparam_ty)) tcs
    ) ax.ax_tparams in
  if tc_binders = [] then
    add_axiom (genv, lenv) (preid_p p) ax.ax_spec
  else begin
    (* Build a dict vsymbol per binder and extend le_tdict. *)
    let lenv, dict_vss =
      List.fold_left (fun (lenv, acc) (tparam_id, offset, tc, tparam_ty) ->
        let w3cd = trans_class genv tc.EcAst.tc_name in
        let dict_ty = WTy.ty_app w3cd.wcd_ts [tparam_ty] in
        let dict_vs =
          WTerm.create_vsymbol
            (WIdent.id_fresh
               (Printf.sprintf "d_%s_%s_%d"
                  (EcIdent.name tparam_id)
                  (EcPath.basename tc.EcAst.tc_name) offset))
            dict_ty in
        let dict_term = WTerm.t_var dict_vs in
        let lenv =
          { lenv with
            le_tdict =
              (DKVar tparam_id, offset, dict_term, w3cd) :: lenv.le_tdict } in
        lenv, (dict_vs, dict_term, w3cd) :: acc
      ) (lenv, []) tc_binders in
    let dict_vss = List.rev dict_vss in
    (* Build body: forall ds. (axioms holds) -> <translated body>. *)
    let w_body = Cast.force_prop (trans_form (genv, lenv) ax.ax_spec) in
    let w_body =
      List.fold_right (fun (_, dict_term, w3cd) acc ->
        let premise = WTerm.ps_app w3cd.wcd_axioms [dict_term] in
        WTerm.t_implies premise acc
      ) dict_vss w_body in
    let w_body =
      WTerm.t_forall_close
        (List.map (fun (vs, _, _) -> vs) dict_vss) [] w_body in
    let pr = WDecl.create_prsymbol (preid_p p) in
    let decl = WDecl.create_prop_decl WDecl.Paxiom pr w_body in
    genv.te_task <- WTask.add_decl genv.te_task decl
  end

(* Phase B — for ONE registered chain-instance path, lazily emit:
   1. A dict const of type [<inst_class>_dict <carrier>] (opaque).
   2. Register the dict in [genv.te_idict] keyed by inst_path so
      Phase D's [try_dict_proj] picks it up for Fops with TCIConcrete
      witness.
   3. Bridge axioms equating each projection on this dict to the user-
      provided concrete realisation (from [anc_symbols]).
   4. The [<class>_axioms <dict>] axiom-hold fact (so polymorphic
      lemmas with [<class>_axioms] premise can be instantiated here).

   Lazy emission keeps the why3 task small: instances unrelated to
   the current goal are never emitted, so SMT solvers aren't slowed
   by a forest of irrelevant dict types + bridges + axhold facts. *)
let sanitize_for_id s =
  String.map (fun c ->
    if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
       || (c >= '0' && c <= '9') || c = '_'
    then c else '_') s

(* Chain walker variant of [ancestors_with_renaming] that ALSO returns
   the [lift] (path indices into tc_prts) used to reach each ancestor.
   Used by Phase B/C to instantiate ancestor axioms at the right chain
   leg — the lift carries the diamond-leg context that the rename map
   alone doesn't. *)
let ancestors_with_lifts
  (env : EcEnv.env) (tc : EcAst.typeclass)
  : (EcAst.typeclass * int list
     * (EcSymbols.symbol * EcSymbols.symbol) list) list
=
  let parents tc =
    let decl = EcEnv.TypeClass.by_path tc.EcAst.tc_name env in
    let subst =
      List.fold_left2
        (fun s (a, _) etyarg -> Mid.add a etyarg s)
        Mid.empty decl.tc_tparams tc.tc_args in
    List.mapi
      (fun i (p, _lbl, ren) ->
        (i, EcCoreSubst.Tvar.subst_tc subst p, ren))
      decl.tc_prts in
  let ren_eq r1 r2 =
    List.length r1 = List.length r2
    && List.for_all2 (fun (a, b) (c, d) -> a = c && b = d) r1 r2 in
  let same (a, _, ra) (b, _, rb) =
    EcPath.p_equal a.EcAst.tc_name b.EcAst.tc_name && ren_eq ra rb in
  let rec bfs frontier acc =
    match frontier with
    | [] -> List.rev acc
    | (tc, lift, ren) :: rest ->
      if List.exists (same (tc, lift, ren)) acc then bfs rest acc
      else
        let next =
          List.map
            (fun (i, p, p_ren) ->
              (p, lift @ [i],
               EcTypeClass.compose_renaming ~outer:p_ren ~inner:ren))
            (parents tc) in
        bfs (rest @ next) ((tc, lift, ren) :: acc)
  in bfs [(tc, [], [])] []

let emit_instance_dict
  (genv : tenv) (path : EcPath.path) : (WTerm.term * w3_class_decl) option
=
  match Hp.find_opt genv.te_idict path with
  | Some pair -> Some pair
  | None ->
  let env = genv.te_env in
  let tci_opt =
    List.find_opt (fun (p, _) ->
      match p with Some p' -> EcPath.p_equal p' path | None -> false)
      (EcEnv.TcInstance.get_all env) in
  match tci_opt with
  | None | Some (_, { EcTheory.tci_instance = `Ring _; _ })
  | Some (_, { EcTheory.tci_instance = `Field _; _ })
  | Some (_, { EcTheory.tci_instance = `General (_, None); _ }) -> None
  | Some (_, ({ EcTheory.tci_instance =
                `General (anc, Some symbols); _ } as tci))
    when tci.EcTheory.tci_params = [] ->
    let w3cd = trans_class genv anc.EcAst.tc_name in
    let carrier_w3_ty = trans_ty (genv, empty_lenv) tci.EcTheory.tci_type in
    let dict_ty = WTy.ty_app w3cd.wcd_ts [carrier_w3_ty] in
    let dict_id =
      WIdent.id_fresh
        (Printf.sprintf "inst_%s" (sanitize_for_id (EcPath.tostring path))) in
    let dict_ls = WTerm.create_lsymbol dict_id [] (Some dict_ty) in
    genv.te_task <- WTask.add_param_decl genv.te_task dict_ls;
    let dict_term = WTerm.fs_app dict_ls [] dict_ty in
    Hp.add genv.te_idict path (dict_term, w3cd);
    (* Axhold. *)
    let hold_pid =
      WIdent.id_fresh
        (Printf.sprintf "axhold_%s" (sanitize_for_id (EcPath.tostring path))) in
    let hold_term = WTerm.ps_app w3cd.wcd_axioms [dict_term] in
    let hold_pr = WDecl.create_prsymbol hold_pid in
    let hold_decl =
      WDecl.create_prop_decl WDecl.Paxiom hold_pr hold_term in
    genv.te_task <- WTask.add_decl genv.te_task hold_decl;
    (* Bridges. With [te_idict] now containing this entry, the LHS
       Fop will translate through [try_dict_proj] to a projection on
       [dict_term]. *)
    let anc_prefix = EcPath.prefix anc.EcAst.tc_name in
    let inst_etyargs = EcDecl.etyargs_of_tparams tci.EcTheory.tci_params in
    EcMaps.Mstr.iter (fun basename rhs_body ->
      let class_op_path = EcPath.pqoname anc_prefix basename in
      match EcEnv.Op.by_path_opt class_op_path env with
      | Some class_op ->
        let witness =
          EcAst.TCIConcrete
            { path    = path;
              etyargs = inst_etyargs;
              lift    = []; } in
        let lhs_etyargs = [(tci.EcTheory.tci_type, [witness])] in
        let lhs_ty =
          EcDecl.ty_instanciate class_op.op_tparams lhs_etyargs class_op.op_ty in
        let dom, codom = EcTypes.tyfun_flat lhs_ty in
        let xs = List.map (fun ty -> (EcIdent.create "x", ty)) dom in
        let xs_forms = List.map (fun (x, ty) -> EcCoreFol.f_local x ty) xs in
        let lhs_head = EcCoreFol.f_op_tc class_op_path lhs_etyargs lhs_ty in
        let lhs = EcCoreFol.f_app lhs_head xs_forms codom in
        let rhs = EcCoreFol.f_app rhs_body xs_forms codom in
        let body = EcCoreFol.f_eq lhs rhs in
        let body =
          EcCoreFol.f_forall
            (List.map (fun (x, ty) -> (x, EcAst.GTty ty)) xs) body in
        let name =
          Printf.sprintf "tcbridge_%s_%s"
            (sanitize_for_id (EcPath.tostring path)) basename in
        add_axiom (genv, empty_lenv) (WIdent.id_fresh name) body
      | _ -> ()
    ) symbols;
    (* Emit each chain ancestor's class axioms INSTANTIATED at this
       instance's concrete carrier and realisations. Without this,
       obligation proofs (where the obligation IS a class axiom at
       the instance) have no way to discharge — the legacy unsound
       encoding relied on bridge-collision False; this sound encoding
       provides the class laws as concrete facts about the instance's
       realisations. The axioms are translated with [te_idict] now
       containing this entry, so Fops of class ops translate to dict
       projections, which the bridges then equate to the realisations.
    *)
    let self_tc =
      let decl = EcEnv.TypeClass.by_path anc.EcAst.tc_name genv.te_env in
      { EcAst.tc_name = anc.EcAst.tc_name;
        tc_args =
          EcDecl.etyargs_of_tparams decl.EcDecl.tc_tparams; } in
    let entries = ancestors_with_lifts env self_tc in
    let inst_self_witness : EcAst.tcwitness =
      EcAst.TCIConcrete { path; etyargs = inst_etyargs; lift = [] } in
    List.iter (fun (anc2, lift_to_anc2, _ren) ->
      let anc2_prefix = EcPath.prefix anc2.EcAst.tc_name in
      List.iter (fun (axname, _) ->
        let ax_path = EcPath.pqoname anc2_prefix axname in
        match EcEnv.Ax.by_path_opt ax_path env with
        | None -> ()
        | Some ax ->
        match List.rev ax.EcDecl.ax_tparams with
        | [] -> ()
        | (self_id, _) :: _ ->
        let our_etyarg : EcAst.etyarg =
          (tci.EcTheory.tci_type,
           [EcAst.bump_lift lift_to_anc2 inst_self_witness]) in
        let subst_map = Mid.singleton self_id our_etyarg in
        let axform' =
          EcCoreSubst.Fsubst.f_subst_tvar ~freshen:true subst_map ax.ax_spec in
        (* Reduce TC ops at concrete carriers. The substituted axiom
           now has TCIConcrete witnesses pointing to this instance and
           its chain ancestors. [delta_tc] resolves these to the
           user-provided concrete realisations (CoreInt.add, etc.),
           so the axiom becomes a pure fact about those concretes —
           it matches obligation goals (which are similarly reduced)
           and other concrete-carrier goals. *)
        let axform' =
          let ri = { EcReduction.no_red with delta_tc = true } in
          let ldecl = EcEnv.LDecl.init env [] in
          EcReduction.simplify ri ldecl axform' in
        let ax_pid =
          WIdent.id_fresh
            (Printf.sprintf "tcinstax_%s_%s"
               (sanitize_for_id (EcPath.tostring path)) axname) in
        add_axiom (genv, empty_lenv) ax_pid axform'
      ) (EcEnv.TypeClass.by_path anc2.EcAst.tc_name env).EcDecl.tc_axs
    ) entries;
    Some (dict_term, w3cd)
  | _ -> None

let () = emit_instance_dict_ref := emit_instance_dict

(* For each typeclass constraint on a goal-context type parameter, pull
   in the typeclass axioms (and those of all its ancestors) as Why3
   axioms. The axioms are registered globally with [`NoSmt] visibility
   so the relevance heuristic skips them; we add them here on a
   per-tparam basis so [smt()] (without explicit hints) can still close
   goals over abstract TC carriers. *)
let trans_tc_axioms genv (tparams : ty_params) =
  let seen = ref EcPath.Sp.empty in
  let trans_one tc =
    let ancestors = EcTypeClass.ancestors genv.te_env tc in
    List.iter (fun anc ->
      match EcEnv.TypeClass.by_path_opt anc.tc_name genv.te_env with
      | None -> ()
      | Some tc_decl ->
        List.iter (fun (axname, _) ->
          let ax_path =
            EcPath.pqoname (EcPath.prefix anc.tc_name) axname in
          if not (EcPath.Sp.mem ax_path !seen) then begin
            seen := EcPath.Sp.add ax_path !seen;
            EcEnv.Ax.by_path_opt ax_path genv.te_env
            |> Option.iter (fun ax -> trans_axiom genv (ax_path, ax))
          end
        ) tc_decl.tc_axs
    ) ancestors in
  List.iter (fun (_, tcs) -> List.iter trans_one tcs) tparams

(* -------------------------------------------------------------------- *)
(* Phase C — emit a fresh why3 dict constant + projected ancestor
   axioms for one [(carrier, offset, class)] triple, registered in
   [lenv.le_tdict] so Phase D's [try_dict_proj] picks it up.

   [carrier_key] / [carrier_ty] / [carrier_ec_ty] / [carrier_name] are
   the four views of the carrier:
     - [carrier_key]: how Fop witnesses key into [le_tdict];
     - [carrier_ty]: why3 type used to instantiate the dict;
     - [carrier_ec_ty]: EC-level type used as the substituted-tparam in
       ancestor axiom translations (so Fops' carriers resolve to the
       in-scope dict);
     - [carrier_name]: short string for the why3 const's id (debugging). *)
let emit_one_dict
    (genv : tenv) (lenv : lenv)
    (carrier_key : dict_carrier)
    (carrier_ty : WTy.ty)
    (carrier_ec_ty : EcAst.ty)
    (carrier_name : string)
    (offset : int)
    (tc : EcAst.typeclass)
  : lenv
=
  let w3cd = trans_class genv tc.EcAst.tc_name in
  let dict_ty = WTy.ty_app w3cd.wcd_ts [carrier_ty] in
  let dict_id =
    WIdent.id_fresh
      (Printf.sprintf "d_%s_%s_%d"
         carrier_name
         (EcPath.basename tc.EcAst.tc_name)
         offset) in
  let dict_ls = WTerm.create_lsymbol dict_id [] (Some dict_ty) in
  genv.te_task <- WTask.add_param_decl genv.te_task dict_ls;
  let dict_term = WTerm.fs_app dict_ls [] dict_ty in
  (* Axioms-hold: assert the uninterpreted [<class>_axioms] predicate
     holds for this dict. Without it, polymorphic lemmas pulled in via
     [smt(...)] (whose translation has [<class>_axioms 'a d] as a
     premise) can't be instantiated at this carrier+dict. *)
  let hold_pid =
    WIdent.id_fresh
      (Printf.sprintf "axhold_%s_%s_%d"
         carrier_name
         (EcPath.basename tc.EcAst.tc_name)
         offset) in
  let hold_term = WTerm.ps_app w3cd.wcd_axioms [dict_term] in
  let hold_pr = WDecl.create_prsymbol hold_pid in
  let hold_decl =
    WDecl.create_prop_decl WDecl.Paxiom hold_pr hold_term in
  genv.te_task <- WTask.add_decl genv.te_task hold_decl;
  (* Register the dict so Phase D's [try_dict_proj] sees it. Tparam
     dicts live in [lenv.le_tdict] (per-goal). Declared-abstract-type
     dicts ALSO live in [tenv.te_absdict] (tenv-level) so lemma and
     op-body translations see them too — axiom bodies referencing a
     section-declared `t::comring` must project through the SAME dict
     the goal uses, or the LHS/RHS of an equation between an axiom
     fact and a goal hypothesis won't have a common why3 symbol. *)
  let lenv' =
    let lenv =
      { lenv with
        le_tdict =
          (carrier_key, offset, dict_term, w3cd) :: lenv.le_tdict; } in
    begin match carrier_key with
    | DKAbs p -> Hashtbl.replace genv.te_absdict (p, offset) (dict_term, w3cd)
    | DKVar _ -> ()
    end;
    lenv in
  (* Build the etyarg for [carrier]: this is what substitutes the
     ancestor-class's tparam in each axiom form, so all Fops in the
     axiom resolve their carrier-witness via OUR dict. *)
  let our_witness : EcAst.tcwitness =
    match carrier_key with
    | DKVar id ->
      EcAst.TCIAbstract { support = `Var id; offset; lift = [] }
    | DKAbs p ->
      EcAst.TCIAbstract { support = `Abs p; offset; lift = [] } in
  let self_tc =
    let decl = EcEnv.TypeClass.by_path tc.EcAst.tc_name genv.te_env in
    { EcAst.tc_name = tc.EcAst.tc_name;
      tc_args =
        EcDecl.etyargs_of_tparams decl.EcDecl.tc_tparams; } in
  let entries = ancestors_with_lifts genv.te_env self_tc in
  List.iter (fun (anc, lift_to_anc, _ren) ->
    let anc_decl =
      EcEnv.TypeClass.by_path anc.EcAst.tc_name genv.te_env in
    let anc_prefix = EcPath.prefix anc.EcAst.tc_name in
    (* For each axiom name, look up the BOUND axiom (env-bound, with
       fresh [self_id] as last tparam). Substitute that [self_id] with
       our carrier (incl. [lift_to_anc] in the witness) so each Fop's
       carrier projects through OUR dict at the right chain leg. *)
    List.iter (fun (axname, _raw_axform) ->
      let ax_path = EcPath.pqoname anc_prefix axname in
      match EcEnv.Ax.by_path_opt ax_path genv.te_env with
      | None -> ()
      | Some ax ->
      match List.rev ax.EcDecl.ax_tparams with
      | [] -> ()
      | (self_id, _) :: _ ->
      let our_etyarg : EcAst.etyarg =
        (carrier_ec_ty,
         [EcAst.bump_lift lift_to_anc our_witness]) in
      let subst_map = Mid.singleton self_id our_etyarg in
      let axform' =
        EcCoreSubst.Fsubst.f_subst_tvar ~freshen:true subst_map ax.ax_spec in
      let ax_pid =
        WIdent.id_fresh
          (Printf.sprintf "tcaxiom_%s_%s_%d_%s"
             carrier_name
             (EcPath.basename tc.EcAst.tc_name)
             offset axname) in
      let w = trans_form (genv, lenv') axform' in
      let pr = WDecl.create_prsymbol ax_pid in
      let decl =
        WDecl.create_prop_decl WDecl.Paxiom pr (Cast.force_prop w) in
      genv.te_task <- WTask.add_decl genv.te_task decl
    ) anc_decl.EcDecl.tc_axs
  ) entries;
  lenv'

(* For each TC bound on a goal hyps' free tparam, emit the dict. *)
let emit_tparam_dicts
    (genv : tenv) (lenv : lenv) (tparams : ty_params) : lenv
=
  List.fold_left (fun lenv (tparam_id, tcs) ->
    let tparam_ty =
      try Mid.find tparam_id lenv.le_tv
      with Not_found -> assert false in
    let carrier_name = EcIdent.name tparam_id in
    List.fold_lefti (fun lenv offset tc ->
      emit_one_dict genv lenv (DKVar tparam_id) tparam_ty
        (EcTypes.tvar tparam_id) carrier_name offset tc
    ) lenv tcs
  ) lenv tparams

(* For each declared-abstract type (e.g. section-introduced
   [declare type t <: comring]) with a TC bound, emit a dict. We
   iterate all such types in the env; this over-pulls but the
   declared-abstract count is small in practice and emit is lazy. *)
let emit_abstract_type_dicts
    (genv : tenv) (lenv : lenv) : lenv
=
  let env = genv.te_env in
  List.fold_left (fun lenv (path, (tydecl : EcDecl.tydecl)) ->
    match tydecl.tyd_type with
    | `Abstract tcs when tcs <> [] && tydecl.tyd_params = [] ->
      let carrier_ty = WTy.ty_app (trans_pty genv path) [] in
      let carrier_ec_ty = EcTypes.tconstr_tc path [] in
      let carrier_name = EcPath.basename path in
      List.fold_lefti (fun lenv offset tc ->
        emit_one_dict genv lenv (DKAbs path) carrier_ty
          carrier_ec_ty carrier_name offset tc
      ) lenv tcs
    | _ -> lenv
  ) lenv (EcEnv.Ty.all env)

(* -------------------------------------------------------------------- *)
let lenv_of_hyps genv (hyps : hyps) : lenv =
  let lenv = fst (lenv_of_tparams_for_hyp genv hyps.h_tvar) in
  (* Phase C — sound dict-passing axioms for tparams + declared-
     abstract types (replaces legacy [trans_tc_axioms] which erased
     witnesses and produced [idm <> idm = false] at [t::comring]). *)
  let lenv = emit_tparam_dicts genv lenv hyps.h_tvar in
  let lenv = emit_abstract_type_dicts genv lenv in
  snd (List.fold_left trans_hyp (genv, lenv) (List.rev hyps.h_local))

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
      (CI_Int.p_int_mul, "infix *" );
      (CI_Int.p_int_lt , "infix <" );
      (CI_Int.p_int_le , "infix <=")]);

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

let core_ty_theories = [
  ((["map"], "Map"),
     [(CI_Map.p_map, "map")]);
]

let core_match_theories = [
    ((["int"], "EuclideanDivision"),
     [(KProj (KApp (CI_Int.p_int_edivz, [KHole; KHole]), 0), "div");
      (KProj (KApp (CI_Int.p_int_edivz, [KHole; KHole]), 1), "mod")])
]

let core_theories = Lazy.from_fun (fun () ->
  let add_core_theory tbl (thname, operators) =
    let theory = curry P.get_w3_th thname in
    let namesp = theory.WTheory.th_export in
    List.iter (fun (p, name) ->
      Hp.add tbl p (WTheory.ns_find_ls namesp [name], theory))
      operators
  in
  let known = Hp.create 27 in
  Hp.add known CI_Unit.p_tt (WTerm.fs_tuple 0, WTheory.tuple_theory 0);
  List.iter (add_core_theory known) core_theories;
  Hp.add known CI_Distr.p_mu (fs_mu, distr_theory);
  Hp.add known CI_Witness.p_witness (fs_witness, witness_theory);

  let add_core_ty tbl (thname, tys) =
    let theory = curry P.get_w3_th thname in
    let namesp = theory.WTheory.th_export in
    List.iter (fun (p, name) ->
      Hp.add tbl p (WTheory.ns_find_ts namesp [name], theory))
      tys in
  let ty_known = Hp.create 7 in
  List.iter (add_core_ty ty_known) core_ty_theories;

  let add_kwk thname (k, name) =
    let theory = curry P.get_w3_th thname in
    let namesp = theory.WTheory.th_export in
    (k, (WTheory.ns_find_ls namesp [name], theory))
  in

  let kwk =
    List.rev (List.flatten
      (List.map
         (fun (wth, syms) -> List.map (add_kwk wth) syms)
         core_match_theories)) in

  ty_known, known, kwk
)

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
      w3op_ta = (fun tys -> let ty = Some (as_seq1 tys) in [], [ty;ty], None);
      w3op_ho = `HO_TODO ("eq", WTerm.ps_equ.WTerm.ls_args, None);
    }

    in Hp.add env.te_op CI_Bool.p_eq w3o_eq
  end;

  (* Add symbol for map *)
  begin
    (* Add Map theory *)
    let th_map = P.get_w3_th ["map"] "Map" in
    let namesp = th_map.WTheory.th_export in
    Hp.add env.te_ty CI_Map.p_map (WTheory.ns_find_ts namesp ["map"]);
  end;

  (* Add modules stuff *)
  env.te_task <- WTask.add_ty_decl env.te_task ts_mem

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
  ]

(* -------------------------------------------------------------------- *)
(* See "Lightweight Relevance Filtering for Machine-Generated           *)
(* Resolution Problems" for a description of axioms selection.          *)

module Frequency = struct

  (* -------------------------------------------------------------------- *)
  type relevant = Sp.t * Sx.t

  let r_empty = Sp.empty, Sx.empty
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
      | Fif      (f1, f2, f3) -> List.iter doit [f1; f2; f3]
      | Fmatch   (b, fs, _)   -> List.iter doit (b :: fs)
      | Flet     (_, f1, f2)  -> List.iter doit [f1; f2]
      | Fapp     (e, es)      -> List.iter doit (e :: es)
      | Ftuple   es           -> List.iter doit es
      | Fproj    (e, _)       -> doit e

      | FhoareF _   | FhoareS _
      | FeHoareF _ | FeHoareS _
      | FbdHoareF _ | FbdHoareS _
      | FequivF _   | FequivS _
      | FeagerF _ -> ()

      | Fpr pr ->
        sf := Sx.add pr.pr_fun !sf;
        doit pr.pr_event.inv; doit pr.pr_args in
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

  let f_ops_oper unwanted_op env p rs =
    match EcEnv.Op.by_path_opt p env with
    | Some op -> begin
      if op.op_opaque.smt then
        rs
      else
        match op with
        | {op_kind = OB_pred (Some (PR_Plain f)) } ->
          r_union rs (f_ops unwanted_op f)
        | {op_kind = OB_oper (Some (OP_Plain f)) } ->
          r_union rs (f_ops unwanted_op f)
        | {op_kind = OB_oper (Some (OP_Fix e)) } ->
          let rec aux rs = function
            | OPB_Leaf (_, e) -> r_union rs (f_ops unwanted_op (form_of_expr e))
            | OPB_Branch bs -> Parray.fold_left (fun rs b -> aux rs b.opb_sub) rs bs
          in
          aux rs e.opf_branches
        | {op_kind = OB_pred (Some (PR_Ind pri)) } ->
          let for1 rs ctor =
            List.fold_left
              (fun rs f -> r_union rs (f_ops unwanted_op f))
              rs ctor.prc_spec
          in List.fold_left for1 rs pri.pri_ctors
        | _ -> rs
        end

      | None ->
        rs

  (* -------------------------------------------------------------------- *)
  type frequency = {
    f_unwanted_op : Sp.t;
    f_tabp : int Hp.t;
    f_tabf : int Hx.t;
  }

  let add fr form =
    let addp p =
      if not (Sp.mem p fr.f_unwanted_op) then
        let n = Hp.find_def fr.f_tabp 0 p in
        Hp.replace fr.f_tabp p (n+1) in
    let addx f =
      let n = Hx.find_def fr.f_tabf 0 f in
      Hx.replace fr.f_tabf f (n+1);
      addp CI_Distr.p_mu in

    let rec add f =
      match f.f_node with
      | Fop      (p,_)        -> addp p
      | Fquant   (_ , _ , f1) -> add f1
      | Fif      (f1, f2, f3) -> List.iter add [f1; f2; f3]
      | Fmatch   (b, fs, _)   -> List.iter add (b :: fs)
      | Flet     (_, f1, f2)  -> List.iter add [f1; f2]
      | Fapp     (e, es)      -> List.iter add (e :: es)
      | Ftuple   es           -> List.iter add es
      | Fproj    (e, _)       -> add e
      | Fpr      pr           -> addx pr.pr_fun;add pr.pr_event.inv;add pr.pr_args
      | _ -> () in
    add form

  let create unwanted_op : frequency =
    { f_unwanted_op = unwanted_op;
      f_tabp        = Hp.create 0;
      f_tabf        = Hx.create 0 }

  let init unwanted_op all : frequency =
    let fr = create unwanted_op in
    List.iter (fun (_,ax) -> add fr ax) all;
    fr

  let frequency fr = function
    | `OP p   -> Hp.find_def fr.f_tabp 0 p
    | `PROC f -> Hx.find_def fr.f_tabf 0 f

end

type relevant_info = {
  (*---*) ri_env : EcEnv.env;
  mutable ri_p   : float;
  (*---*) ri_c   : float;
  (*---*) ri_fr  : Frequency.frequency;
  mutable ri_max : int;                   (* maximun number of axioms  *)
  mutable toadd  : (path * axiom) list;
  mutable rs0    : Frequency.relevant;
  mutable rs1    : Frequency.relevant;
}

let push_ax ri ax =
  ri.ri_max <- ri.ri_max - 1;
  ri.toadd  <- ax::ri.toadd

let update_rs ri rel =
  let doax rs (ax, ars) = push_ax ri ax;  Frequency.r_union rs ars in
  let rs = List.fold_left doax ri.rs1 rel in
  let new_s = fst (Frequency.r_diff ri.rs1 ri.rs0) in
  let rs = Sp.fold (Frequency.f_ops_oper unwanted_ops ri.ri_env) new_s rs in
  ri.rs0 <- ri.rs1;
  ri.rs1 <- rs

let init_relevant env pi rs =
  let unwanted_ax p  = P.Hints.mem p pi.P.pr_unwanted in
  let wanted_ax   p  = P.Hints.mem p pi.P.pr_wanted in
  (* [ftab] frequency table number of occurency of operators *)
  let fr = Frequency.create unwanted_ops in
  let rel = ref [] in
  let other = ref [] in
  let push e r = r := e :: !r in
  let do1 p ax =
    let wanted = wanted_ax p in
    if wanted || (ax.ax_smt && not (unwanted_ax p)) then begin
      Frequency.add fr ax.ax_spec;
      let used = Frequency.f_ops unwanted_ops ax.ax_spec in
      let paxu = (p,ax), used in
      if wanted then push paxu rel else push paxu other
    end in
  EcEnv.Ax.iter do1 env;
  let ri = {
    ri_env = env;
    ri_p   = 0.6;
    ri_c   = 2.4;
    ri_fr  = fr;
    ri_max = pi.P.pr_max;
    toadd  = [];
    rs0    = Frequency.r_empty;
    rs1    = rs; } in
  update_rs ri !rel;
  ri, !other

let relevant_clause ri other =
  let symbols_of (_,s) = s in
  let frequency_function freq = 1. +. log1p (float_of_int freq) in

  let clause_mark p other =
    let rel = ref [] in
    let newo = ref [] in
    let do1 ax =
      let cs = symbols_of ax in
      let r  = Frequency.r_inter cs ri.rs1 in
      let ir = Frequency.r_diff cs r in
      let weight path m =
        let freq = Frequency.frequency ri.ri_fr path in
        let w = frequency_function freq in
        m +. w in
      let m = Frequency.r_fold weight r 0. in
      let m = m /. (m +. float_of_int (Frequency.r_card ir)) in
      if p <= m then rel := ax :: !rel else newo := ax :: !newo in
    List.iter do1 other;
    !rel, !newo in

  let rec aux p other =
    if ri.ri_max <= 0 then other
    else
      let rel, other = clause_mark p other in
      if rel = [] then other
      else
        let p = p +. (1. -. p) /. ri.ri_c in
        update_rs ri rel;
        aux p other

  in aux ri.ri_p other

(* -------------------------------------------------------------------- *)
let create_global_task () =
  let task  = (None : WTask.task) in
  let task  = WTask.use_export task WTheory.builtin_theory in
  let task  = WTask.use_export task (WTheory.tuple_theory 0) in
  let task  = WTask.use_export task WTheory.bool_theory in
  let task  = WTask.use_export task WTheory.highord_theory in
  let task  = WTask.use_export task distr_theory in
  let task  = WTask.use_export task witness_theory in
  let thmap = P.get_w3_th ["map"] "Map" in
  let task  = WTask.use_export task thmap in
  task

let dump_why3 (env : EcEnv.env) (filename : string) =
  let known = Lazy.force core_theories in
  let tenv  = empty_tenv env (create_global_task ()) known in
  let ()    = add_core_bindings tenv in

  List.iter (trans_axiom tenv) (EcEnv.Ax.all env);
  dump_tasks tenv.te_task filename

let init hyps_ld concl =
  let env   = LDecl.toenv hyps_ld in
  (* Pre-reduce TC ops at concrete instances. With this delta_tc pass,
     Fops like [Top.TcMonoid.mop<:int + addmonoid leg>] reduce to
     [CoreInt.add] directly — they NEVER hit Phase D's dict projection
     path, so concrete-carrier goals translate as if they had no TC
     content. Phase D still handles abstract-carrier Fops (which stay
     unreduced). This keeps obligation-discharge proofs working
     soundly: the goal is in concrete terms, matched by the concrete
     bridges/realisations that Phase B emits. *)
  let concl =
    let ri = { EcReduction.no_red with delta_tc = true } in
    EcReduction.simplify ri hyps_ld concl in
  let hyps  = LDecl.tohyps hyps_ld in
  let task  = create_global_task () in
  let known = Lazy.force core_theories in
  let tenv  = empty_tenv env task known in
  let ()    = add_core_bindings tenv in
  (* Phase B — eagerly emit dicts + bridges + axhold for all
     registered reducible instances. Eager so polymorphic lemmas
     pulled in via [smt(hint1 hint2)] have access to the instance
     dicts at concrete carriers. *)
  let ()    =
    List.iter (fun (path_opt, tci) ->
      match path_opt, tci.EcTheory.tci_instance with
      | Some path, `General (_, Some _)
        when tci.EcTheory.tci_params = []
             && tci.EcTheory.tci_reducible ->
        ignore (emit_instance_dict tenv path : _ option)
      | _ -> ()
    ) (EcEnv.TcInstance.get_all env) in
  let lenv  = lenv_of_hyps tenv hyps in
  let wterm = Cast.force_prop (trans_form (tenv, lenv) concl) in
  let pr    = WDecl.create_prsymbol (WIdent.id_fresh "goal") in
  let decl  = WDecl.create_prop_decl WDecl.Pgoal pr wterm in
  env,hyps,tenv,decl

(* -------------------------------------------------------------------- *)

let select env pi hyps concl execute_task =
  if pi.P.pr_all then
    let init_select p ax =
      ax.ax_smt && not (P.Hints.mem p pi.P.pr_unwanted) in
    (execute_task (EcEnv.Ax.all ~check:init_select env) = Some true)
  else
    let rs = Frequency.f_ops_goal unwanted_ops hyps.h_local concl in
    let ri, other = init_relevant env pi rs in
    ignore (relevant_clause ri other);
    (execute_task ri.toadd = Some true)

(* -------------------------------------------------------------------- *)
let cnt = Counter.create ()

let make_task tenv toadd decl=
    List.iter (trans_axiom tenv) toadd;
    WTask.add_decl tenv.te_task decl

let check ?notify (pi : P.prover_infos) (hyps : LDecl.hyps) (concl : form) =
  let out_task filename task =
    let stream = open_out filename in
    EcUtils.try_finally
      (fun () -> Format.fprintf
        (Format.formatter_of_out_channel stream)
        "%a@." Why3.Pretty.print_task task)
      (fun () -> close_out stream) in

  let env,hyps,tenv,decl = init hyps concl in

  let execute_task toadd =
    if pi.P.pr_selected then begin
      let buffer = Buffer.create 0 in
      let fmt    = Format.formatter_of_buffer buffer in
      let ppe    = EcPrinting.PPEnv.ofenv env in
      let l      = List.map fst toadd in
      let pp fmt = EcPrinting.pp_list "@ " (EcPrinting.pp_axname ppe) fmt in
      Format.fprintf fmt "selected lemmas: @[%a@]@." pp l;
      notify |> oiter (fun notify -> notify `Warning
        (lazy (Buffer.contents buffer)))
    end;

    let task = make_task tenv toadd decl in
    let tkid = Counter.next cnt in

    let dumpin_opt =
      match pi.pr_dumpin with
      | None -> Os.getenv "EC_WHY3"
      | Some filename -> Some (EcLocation.unloc filename)
    in
    ( dumpin_opt |> oiter (fun filename ->
          Format.eprintf "dumping in %s" filename;
      let filename = Printf.sprintf "%.4d-%s" tkid filename in
      out_task filename task));
    let (tp, res) = EcUtils.timed (fun task ->
        if Sys.ocaml_release.major = 5 then begin
          let control = Gc.get () in
          Gc.set { control with space_overhead = min 20 control.space_overhead; };
          EcUtils.try_finally
            (fun () -> P.execute_task ?notify pi task)
            (fun () -> Gc.set control)
        end else P.execute_task ?notify pi task
      ) task in

    if 1 <= pi.P.pr_verbose then
      notify |> oiter (fun notify -> notify `Warning (lazy (
        Printf.sprintf "SMT done: %.5f\n%!" tp)));
    res
  in
  select env pi hyps concl execute_task
