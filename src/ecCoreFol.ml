(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcAst
open EcTypes
open EcCoreModules

module BI = EcBigInt
module Mp = EcPath.Mp
module Sp = EcPath.Sp
module Sm = EcPath.Sm
module Sx = EcPath.Sx

open EcBigInt.Notations

(* -------------------------------------------------------------------- *)
type quantif = EcAst.quantif

type hoarecmp = EcAst.hoarecmp

type gty = EcAst.gty

type binding  = (EcIdent.t * gty)
type bindings = binding list

type form     = EcAst.form
type f_node   = EcAst.f_node
type eagerF   = EcAst.eagerF
type equivF   = EcAst.equivF
type equivS   = EcAst.equivS
type sHoareF  = EcAst.sHoareF
type sHoareS  = EcAst.sHoareS
type eHoareF  = EcAst.eHoareF
type eHoareS  = EcAst.eHoareS
type cHoareF  = EcAst.cHoareF
type cHoareS  = EcAst.cHoareS
type bdHoareF = EcAst.bdHoareF
type bdHoareS = EcAst.bdHoareS
type pr       = EcAst.pr
type coe      = EcAst.coe
type cost     = EcAst.cost
(* Call with cost at most [cb_cost], called at mist [cb_called].
   [cb_cost] is here to properly handle substsitution when instantiating an
   abstract module by a concrete one. *)
type call_bound  = EcAst.call_bound

type module_type = EcAst.module_type

type mod_restr = EcAst.mod_restr

(*-------------------------------------------------------------------- *)
let mhr    = EcAst.mhr
let mleft  = EcAst.mleft
let mright = EcAst.mright

(*-------------------------------------------------------------------- *)
let qt_equal = EcAst.qt_equal
let qt_hash  = EcAst.qt_hash

(*-------------------------------------------------------------------- *)
let f_equal = EcAst.f_equal
let f_compare f1 f2 = f2.f_tag - f1.f_tag
let f_hash = EcAst.f_hash
let f_fv   = EcAst.f_fv
let f_ty f = f.f_ty

let mty_equal = EcAst.mty_equal
let mty_hash  = EcAst.mty_hash

let mr_equal = EcAst.mr_equal
let mr_hash  = EcAst.mr_hash

(*-------------------------------------------------------------------- *)
let gty_equal = EcAst.gty_equal
let gty_hash  = EcAst.gty_hash

(* -------------------------------------------------------------------- *)
let mr_fv = EcAst.mr_fv

(* -------------------------------------------------------------------- *)
let gty_fv = EcAst.gty_fv

(* -------------------------------------------------------------------- *)
let gtty (ty : EcTypes.ty) =
  GTty ty

let gtmodty (mt : module_type) =
  GTmodty mt

let gtmem (mt : EcMemory.memtype) =
  GTmem mt

(* -------------------------------------------------------------------- *)
let as_gtty  = function GTty ty  -> ty  | _ -> assert false
let as_modty = function GTmodty mty -> mty | _ -> assert false
let as_mem   = function GTmem m -> m | _ -> assert false

(*-------------------------------------------------------------------- *)
let b_equal = EcAst.b_equal
let b_hash  = EcAst.b_hash

(* -------------------------------------------------------------------- *)
let hcmp_hash = EcAst.hcmp_hash

(*-------------------------------------------------------------------- *)
module MSHf = EcMaps.MakeMSH(struct
  type t = form
  let tag f = f.f_tag
end)

module Mf = MSHf.M
module Sf = MSHf.S
module Hf = MSHf.H

let call_bound_equal = EcAst.call_bound_equal
let cost_equal = EcAst.cost_equal
let hf_equal   = EcAst.hf_equal
let hs_equal   = EcAst.hs_equal
let ehf_equal  = EcAst.ehf_equal
let ehs_equal  = EcAst.ehs_equal
let chf_equal  = EcAst.chf_equal
let chs_equal  = EcAst.chs_equal
let bhf_equal  = EcAst.bhf_equal
let bhs_equal  = EcAst.bhs_equal
let eqf_equal  = EcAst.eqf_equal
let eqs_equal  = EcAst.eqs_equal
let egf_equal  = EcAst.egf_equal
let coe_equal  = EcAst.coe_equal
let pr_equal   = EcAst.pr_equal


(* -------------------------------------------------------------------- *)
let call_bound_hash = EcAst.call_bound_hash
let cost_hash = EcAst.cost_hash
let hf_hash   = EcAst.hf_hash
let hs_hash   = EcAst.hs_hash
let ehf_hash  = EcAst.ehf_hash
let ehs_hash  = EcAst.ehs_hash
let chf_hash  = EcAst.chf_hash
let chs_hash  = EcAst.chs_hash
let bhf_hash  = EcAst.bhf_hash
let bhs_hash  = EcAst.bhs_hash
let ef_hash   = EcAst.ef_hash
let es_hash   = EcAst.es_hash
let eg_hash   = EcAst.eg_hash
let coe_hash  = EcAst.coe_hash
let pr_hash   = EcAst.pr_hash


(* -------------------------------------------------------------------- *)
let gty_as_ty =
  function GTty ty -> ty | _ -> assert false

let gty_as_mem =
  function GTmem m -> m  | _ -> assert false

let gty_as_mod = function GTmodty mt -> mt | _ -> assert false

let kind_of_gty = function
  | GTty    _ -> `Form
  | GTmem   _ -> `Mem
  | GTmodty _ -> `Mod

(* -------------------------------------------------------------------- *)
let hoarecmp_opp cmp =
  match cmp with
  | FHle -> FHge
  | FHeq -> FHeq
  | FHge -> FHle

(* -------------------------------------------------------------------- *)
let mk_form = EcAst.mk_form
let f_node { f_node = form } = form

(* -------------------------------------------------------------------- *)
let f_op x tys ty = mk_form (Fop (x, tys)) ty

let f_app f args ty =
  let f, args' =
    match f.f_node with
    | Fapp (f, args') -> (f, args')
    | _ -> (f, [])
  in let args' = args' @ args in

  if List.is_empty args' then begin
    (*if ty_equal ty f.f_ty then f else mk_form f.f_node ty *) f
  end else mk_form (Fapp (f, args')) ty

(* -------------------------------------------------------------------- *)
let f_local  x ty   = mk_form (Flocal x) ty
let f_pvar   x ty m = mk_form (Fpvar(x, m)) ty
let f_pvloc  v  m = f_pvar (pv_loc v.v_name) v.v_type m

let f_pvarg  ty m = f_pvar pv_arg ty m

let f_pvlocs vs menv = List.map (fun v -> f_pvloc v menv) vs
let f_glob   m mem   = mk_form (Fglob (m, mem)) (tglob m)

(* -------------------------------------------------------------------- *)
let f_tt     = f_op EcCoreLib.CI_Unit.p_tt    [] tunit
let f_true   = f_op EcCoreLib.CI_Bool.p_true  [] tbool
let f_false  = f_op EcCoreLib.CI_Bool.p_false [] tbool
let f_bool   = fun b -> if b then f_true else f_false

(* -------------------------------------------------------------------- *)
let f_tuple args =
  match args with
  | []  -> f_tt
  | [x] -> x
  | _   -> mk_form (Ftuple args) (ttuple (List.map f_ty args))

let f_quant q b f =
  if List.is_empty b then f else
    let (q, b, f) =
      match f.f_node with
      | Fquant(q',b',f') when q = q' -> (q, b@b', f')
      | _ -> q, b , f in
    let ty =
      if   q = Llambda
      then toarrow (List.map (fun (_,gty) -> gty_as_ty gty) b) f.f_ty
      else tbool in

    mk_form (Fquant (q, b, f)) ty

let f_proj   f  i  ty = mk_form (Fproj(f, i)) ty
let f_if     f1 f2 f3 = mk_form (Fif (f1, f2, f3)) f2.f_ty
let f_match  b  fs ty = mk_form (Fmatch (b, fs, ty)) ty
let f_let    q  f1 f2 = mk_form (Flet (q, f1, f2)) f2.f_ty (* FIXME rename binding *)
let f_let1   x  f1 f2 = f_let (LSymbol (x, f1.f_ty)) f1 f2
let f_exists b  f     = f_quant Lexists b f
let f_forall b  f     = f_quant Lforall b f
let f_lambda b  f     = f_quant Llambda b f

let f_forall_mems bds f =
  f_forall (List.map (fun (m, mt) -> (m, GTmem mt)) bds) f

(* -------------------------------------------------------------------- *)
let ty_fbool1 = toarrow (List.make 1 tbool) tbool
let ty_fbool2 = toarrow (List.make 2 tbool) tbool

let fop_not  = f_op EcCoreLib.CI_Bool.p_not  [] ty_fbool1
let fop_and  = f_op EcCoreLib.CI_Bool.p_and  [] ty_fbool2
let fop_anda = f_op EcCoreLib.CI_Bool.p_anda [] ty_fbool2
let fop_or   = f_op EcCoreLib.CI_Bool.p_or   [] ty_fbool2
let fop_ora  = f_op EcCoreLib.CI_Bool.p_ora  [] ty_fbool2
let fop_imp  = f_op EcCoreLib.CI_Bool.p_imp  [] ty_fbool2
let fop_iff  = f_op EcCoreLib.CI_Bool.p_iff  [] ty_fbool2

let f_not  f     = f_app fop_not  [f]      tbool
let f_and  f1 f2 = f_app fop_and  [f1; f2] tbool
let f_anda f1 f2 = f_app fop_anda [f1; f2] tbool
let f_or   f1 f2 = f_app fop_or   [f1; f2] tbool
let f_ora  f1 f2 = f_app fop_ora  [f1; f2] tbool
let f_imp  f1 f2 = f_app fop_imp  [f1; f2] tbool
let f_iff  f1 f2 = f_app fop_iff  [f1; f2] tbool

let f_ands fs =
  match List.rev fs with
  | [] -> f_true
  | f::fs -> List.fold_left ((^~) f_and) f fs

let f_andas fs =
  match List.rev fs with
  | [] -> f_true
  | f::fs -> List.fold_left ((^~) f_anda) f fs

let f_ors fs =
  match List.rev fs with
  | [] -> f_false
  | f::fs -> List.fold_left ((^~) f_or) f fs

let f_oras fs =
  match List.rev fs with
  | [] -> f_false
  | f::fs -> List.fold_left ((^~) f_ora) f fs

let f_imps = List.fold_right f_imp

(* -------------------------------------------------------------------- *)
let fop_eq ty = f_op EcCoreLib.CI_Bool.p_eq [ty] (toarrow [ty; ty] tbool)

let f_eq f1 f2 = f_app (fop_eq f1.f_ty) [f1; f2] tbool

let f_eqs fs1 fs2 =
  assert (List.length fs1 = List.length fs2);
  f_ands (List.map2 f_eq fs1 fs2)

(* -------------------------------------------------------------------- *)
let f_hoareS_r hs = mk_form (FhoareS hs) tbool
let f_hoareF_r hf = mk_form (FhoareF hf) tbool

let f_hoareS hs_m hs_pr hs_s hs_po =
  f_hoareS_r { hs_m; hs_pr; hs_s; hs_po; }

let f_hoareF hf_pr hf_f hf_po =
  f_hoareF_r { hf_pr; hf_f; hf_po; }

(* -------------------------------------------------------------------- *)
let f_eHoareS_r hs = mk_form (FeHoareS hs) tbool
let f_eHoareF_r hf = mk_form (FeHoareF hf) tbool

let f_eHoareS ehs_m ehs_pr ehs_s ehs_po =
  f_eHoareS_r { ehs_m; ehs_pr; ehs_s; ehs_po; }

let f_eHoareF ehf_pr ehf_f ehf_po =
  f_eHoareF_r { ehf_pr; ehf_f; ehf_po; }

(* -------------------------------------------------------------------- *)
let call_bound_r cb_cost cb_called =
  { cb_cost; cb_called }

let cost_r c_self c_calls =
  (* Invariant: keys of c_calls are functions of local modules,
     with no arguments. *)
  assert (EcPath.Mx.for_all (fun x _ ->
      match x.x_top.m_top with
      | `Local _ -> x.x_top.m_args = []
      | _ -> false
    ) c_calls);
  let c = { c_self; c_calls; } in
  c

let f_cHoareS_r chs = mk_form (FcHoareS chs) tbool
let f_cHoareF_r chf = mk_form (FcHoareF chf) tbool

let f_cHoareS chs_m chs_pr chs_s chs_po chs_co =
  f_cHoareS_r { chs_m; chs_pr; chs_s; chs_po; chs_co }

let f_cHoareF chf_pr chf_f chf_po chf_co =
  f_cHoareF_r { chf_pr; chf_f; chf_po; chf_co }

(* -------------------------------------------------------------------- *)
let f_bdHoareS_r bhs = mk_form (FbdHoareS bhs) tbool
let f_bdHoareF_r bhf = mk_form (FbdHoareF bhf) tbool

let f_bdHoareS bhs_m bhs_pr bhs_s bhs_po bhs_cmp bhs_bd =
  f_bdHoareS_r
    { bhs_m; bhs_pr; bhs_s; bhs_po; bhs_cmp; bhs_bd; }

let f_bdHoareF bhf_pr bhf_f bhf_po bhf_cmp bhf_bd =
  f_bdHoareF_r { bhf_pr; bhf_f; bhf_po; bhf_cmp; bhf_bd; }

(* -------------------------------------------------------------------- *)
let f_equivS_r es = mk_form (FequivS es) tbool
let f_equivF_r ef = mk_form (FequivF ef) tbool

let f_equivS es_ml es_mr es_pr es_sl es_sr es_po =
   f_equivS_r { es_ml; es_mr; es_pr; es_sl; es_sr; es_po; }

let f_equivF ef_pr ef_fl ef_fr ef_po =
  f_equivF_r{ ef_pr; ef_fl; ef_fr; ef_po; }

(* -------------------------------------------------------------------- *)
let f_eagerF_r eg = mk_form (FeagerF eg) tbool

let f_eagerF eg_pr eg_sl eg_fl eg_fr eg_sr eg_po =
  f_eagerF_r { eg_pr; eg_sl; eg_fl; eg_fr; eg_sr; eg_po; }

(* -------------------------------------------------------------------- *)
let f_coe_r coe = mk_form (Fcoe coe) txint

let f_coe coe_pre coe_mem coe_e = f_coe_r { coe_pre; coe_mem; coe_e; }

(* -------------------------------------------------------------------- *)
let f_pr_r pr = mk_form (Fpr pr) treal

let f_pr pr_mem pr_fun pr_args pr_event =
  f_pr_r { pr_mem; pr_fun; pr_args; pr_event; }

(* -------------------------------------------------------------------- *)
let fop_int_opp   = f_op EcCoreLib.CI_Int.p_int_opp [] (toarrow [tint]       tint)
let fop_int_add   = f_op EcCoreLib.CI_Int.p_int_add [] (toarrow [tint; tint] tint)
let fop_int_mul   = f_op EcCoreLib.CI_Int.p_int_mul [] (toarrow [tint; tint] tint)
let fop_int_pow   = f_op EcCoreLib.CI_Int.p_int_pow [] (toarrow [tint; tint] tint)

let fop_int_edivz =
  f_op EcCoreLib.CI_Int.p_int_edivz []
       (toarrow [tint; tint] (ttuple [tint; tint]))

let f_int_opp   f     = f_app fop_int_opp [f]      tint
let f_int_add   f1 f2 = f_app fop_int_add [f1; f2] tint
let f_int_mul   f1 f2 = f_app fop_int_mul [f1; f2] tint
let f_int_pow   f1 f2 = f_app fop_int_pow [f1; f2] tint
let f_int_edivz f1 f2 = f_app fop_int_edivz [f1; f2] tint

let f_int_sub f1 f2 =
  f_int_add f1 (f_int_opp f2)

let rec f_int (n : BI.zint) =
  match BI.sign n with
  | s when 0 <= s -> mk_form (Fint n) tint
  | _             -> f_int_opp (f_int (~^ n))

(* -------------------------------------------------------------------- *)
let f_i0  = f_int BI.zero
let f_i1  = f_int BI.one
let f_im1 = f_int_opp f_i1

(* -------------------------------------------------------------------- *)
let f_op_xopp   = f_op EcCoreLib.CI_xint.p_xopp  [] (toarrow [txint        ] txint)
let f_op_xadd   = f_op EcCoreLib.CI_xint.p_xadd  [] (toarrow [txint; txint ] txint)
let f_op_xmul   = f_op EcCoreLib.CI_xint.p_xmul  [] (toarrow [txint; txint ] txint)
let f_op_xle    = f_op EcCoreLib.CI_xint.p_xle   [] (toarrow [txint; txint ] tbool)
let f_op_xmax   = f_op EcCoreLib.CI_xint.p_xmax  [] (toarrow [txint;  txint] txint)

let f_op_inf    = f_op EcCoreLib.CI_xint.p_inf    [] txint
let f_op_N      = f_op EcCoreLib.CI_xint.p_N      [] (toarrow [tint ] txint)
let f_op_is_inf = f_op EcCoreLib.CI_xint.p_is_inf [] (toarrow [txint] tbool)
let f_op_is_int = f_op EcCoreLib.CI_xint.p_is_int [] (toarrow [txint] tbool)

let f_is_inf f  = f_app f_op_is_inf [f] tbool
let f_is_int f  = f_app f_op_is_int [f] tbool

let f_Inf         = f_app f_op_inf  []       txint
let f_N     f     = f_app f_op_N    [f]      txint
let f_xopp  f     = f_app f_op_xopp [f]      txint
let f_xadd  f1 f2 = f_app f_op_xadd [f1; f2] txint
let f_xmul  f1 f2 = f_app f_op_xmul [f1; f2] txint
let f_xmuli fi f  = f_xmul (f_N fi) f
let f_xle   f1 f2 = f_app f_op_xle  [f1; f2] tbool
let f_xmax  f1 f2 = f_app f_op_xmax [f1; f2] txint

let f_x0 = f_N f_i0
let f_x1 = f_N f_i1

let f_xadd_simpl f1 f2 =
  if f_equal f1 f_x0 then f2 else
  if f_equal f2 f_x0 then f1 else f_xadd f1 f2

let f_xmul_simpl f1 f2 =
  if   f_equal f1 f_x0 || f_equal f2 f_x0
  then f_x0
  else f_xmul f1 f2

let f_xmuli_simpl f1 f2 =
  f_xmul_simpl (f_N f1) f2

(* -------------------------------------------------------------------- *)
let f_none (ty : ty) : form =
  f_op EcCoreLib.CI_Option.p_none [ty] (toption ty)

let f_some ({ f_ty = ty } as f : form) : form =
  let op = f_op EcCoreLib.CI_Option.p_some [ty] (tfun ty (toption ty)) in
  f_app op [f] (toption ty)

(* -------------------------------------------------------------------- *)
let cost_map g cost =
  let calls =
    EcPath.Mx.map (fun cb ->
        { cb_cost  = g cb.cb_cost;
          cb_called = g cb.cb_called }
      ) cost.c_calls in

  cost_r (g cost.c_self) calls

let cost_iter g cost =
  g cost.c_self;
  EcPath.Mx.iter (fun _ cb -> g cb.cb_cost; g cb.cb_called; ) cost.c_calls

let f_map gt g fp =
  match fp.f_node with
  | Fquant(q, b, f) ->
      let map_gty ((x, gty) as b1) =
        let gty' =
          match gty with
          | GTty ty ->
              let ty' = gt ty in if ty == ty' then gty else GTty ty'
          | _ -> gty
        in
          if gty == gty' then b1 else (x, gty')
      in

      let b' = List.Smart.map map_gty b in
      let f' = g f in

      f_quant q b' f'

  | Fint  _ -> fp
  | Fglob _ -> fp

  | Fif (f1, f2, f3) ->
      f_if (g f1) (g f2) (g f3)

  | Fmatch (b, fs, ty) ->
      f_match (g b) (List.map g fs) (gt ty)

  | Flet (lp, f1, f2) ->
      f_let lp (g f1) (g f2)

  | Flocal id ->
      let ty' = gt fp.f_ty in
        f_local id ty'

  | Fpvar (id, s) ->
      let ty' = gt fp.f_ty in
        f_pvar id ty' s

  | Fop (p, tys) ->
      let tys' = List.Smart.map gt tys in
      let ty'  = gt fp.f_ty in
        f_op p tys' ty'

  | Fapp (f, fs) ->
      let f'  = g f in
      let fs' = List.Smart.map g fs in
      let ty' = gt fp.f_ty in
        f_app f' fs' ty'

  | Ftuple fs ->
      let fs' = List.Smart.map g fs in
        f_tuple fs'

  | Fproj (f, i) ->
      let f'  = g f in
      let ty' = gt fp.f_ty in
        f_proj f' i ty'

  | FhoareF hf ->
      let pr' = g hf.hf_pr in
      let po' = g hf.hf_po in
        f_hoareF_r { hf with hf_pr = pr'; hf_po = po'; }

  | FhoareS hs ->
      let pr' = g hs.hs_pr in
      let po' = g hs.hs_po in
        f_hoareS_r { hs with hs_pr = pr'; hs_po = po'; }

  | FeHoareF hf ->
      let pr' = g hf.ehf_pr  in
      let po' = g hf.ehf_po  in
      f_eHoareF_r { hf with ehf_pr = pr'; ehf_po = po' }

  | FeHoareS hs ->
      let pr' = g hs.ehs_pr  in
      let po' = g hs.ehs_po  in
        f_eHoareS_r { hs with ehs_pr = pr'; ehs_po = po'; }

  | FcHoareF chf ->
      let pr' = g chf.chf_pr in
      let po' = g chf.chf_po in
      let c'  = cost_map g chf.chf_co in
        f_cHoareF_r { chf with chf_pr = pr'; chf_po = po'; chf_co = c' }

  | FcHoareS chs ->
      let pr' = g chs.chs_pr in
      let po' = g chs.chs_po in
      let c'  = cost_map g chs.chs_co in
        f_cHoareS_r { chs with chs_pr = pr'; chs_po = po'; chs_co = c' }

  | FbdHoareF bhf ->
      let pr' = g bhf.bhf_pr in
      let po' = g bhf.bhf_po in
      let bd' = g bhf.bhf_bd in
        f_bdHoareF_r { bhf with bhf_pr = pr'; bhf_po = po'; bhf_bd = bd'; }

  | FbdHoareS bhs ->
      let pr' = g bhs.bhs_pr in
      let po' = g bhs.bhs_po in
      let bd' = g bhs.bhs_bd in
        f_bdHoareS_r { bhs with bhs_pr = pr'; bhs_po = po'; bhs_bd = bd'; }

  | FequivF ef ->
      let pr' = g ef.ef_pr in
      let po' = g ef.ef_po in
        f_equivF_r { ef with ef_pr = pr'; ef_po = po'; }

  | FequivS es ->
      let pr' = g es.es_pr in
      let po' = g es.es_po in
        f_equivS_r { es with es_pr = pr'; es_po = po'; }

  | FeagerF eg ->
      let pr' = g eg.eg_pr in
      let po' = g eg.eg_po in
        f_eagerF_r { eg with eg_pr = pr'; eg_po = po'; }

  | Fcoe coe ->
    let pre' = g coe.coe_pre in
    f_coe_r { coe with coe_pre = pre'; }

  | Fpr pr ->
      let args' = g pr.pr_args in
      let ev'   = g pr.pr_event in
      f_pr_r { pr with pr_args = args'; pr_event = ev'; }

(* -------------------------------------------------------------------- *)
let f_iter g f =
  match f.f_node with
  | Fint     _
  | Flocal   _
  | Fpvar    _
  | Fglob    _
  | Fop      _ -> ()

  | Fquant   (_ , _ , f1) -> g f1
  | Fif      (f1, f2, f3) -> g f1;g f2; g f3
  | Fmatch   (b, fs, _)   -> List.iter g (b :: fs)
  | Flet     (_, f1, f2)  -> g f1;g f2
  | Fapp     (e, es)      -> List.iter g (e :: es)
  | Ftuple   es           -> List.iter g es
  | Fproj    (e, _)       -> g e

  | FhoareF  hf   -> g hf.hf_pr; g hf.hf_po
  | FhoareS  hs   -> g hs.hs_pr; g hs.hs_po
  | FcHoareF  chf -> g chf.chf_pr; g chf.chf_po; cost_iter g chf.chf_co
  | FcHoareS  chs -> g chs.chs_pr; g chs.chs_po; cost_iter g chs.chs_co
  | FeHoareF  hf  -> g hf.ehf_pr; g hf.ehf_po
  | FeHoareS  hs  -> g hs.ehs_pr; g hs.ehs_po
  | FbdHoareF bhf -> g bhf.bhf_pr; g bhf.bhf_po; g bhf.bhf_bd
  | FbdHoareS bhs -> g bhs.bhs_pr; g bhs.bhs_po; g bhs.bhs_bd
  | FequivF   ef  -> g ef.ef_pr; g ef.ef_po
  | FequivS   es  -> g es.es_pr; g es.es_po
  | FeagerF   eg  -> g eg.eg_pr; g eg.eg_po
  | Fcoe      coe -> g coe.coe_pre;
  | Fpr       pr  -> g pr.pr_args; g pr.pr_event


(* -------------------------------------------------------------------- *)
let form_exists g f =
  match f.f_node with
  | Fint     _
  | Flocal   _
  | Fpvar    _
  | Fglob    _
  | Fop      _ -> false

  | Fquant   (_ , _ , f1) -> g f1
  | Fif      (f1, f2, f3) -> g f1 || g f2 || g f3
  | Fmatch   (b, fs, _)   -> List.exists g (b :: fs)
  | Flet     (_, f1, f2)  -> g f1 || g f2
  | Fapp     (e, es)      -> List.exists g (e :: es)
  | Ftuple   es           -> List.exists g es
  | Fproj    (e, _)       -> g e

  | FhoareF   hf -> g hf.hf_pr   || g hf.hf_po
  | FhoareS   hs -> g hs.hs_pr   || g hs.hs_po
  | FcHoareF  chf -> g chf.chf_pr  || g chf.chf_po
  | FcHoareS  chs -> g chs.chs_pr  || g chs.chs_po
  | FeHoareF  hf  -> g hf.ehf_pr || g hf.ehf_po
  | FeHoareS  hs  -> g hs.ehs_pr || g hs.ehs_po
  | FbdHoareF bhf -> g bhf.bhf_pr  || g bhf.bhf_po
  | FbdHoareS bhs -> g bhs.bhs_pr  || g bhs.bhs_po
  | FequivF   ef  -> g ef.ef_pr    || g ef.ef_po
  | FequivS   es  -> g es.es_pr    || g es.es_po
  | FeagerF   eg  -> g eg.eg_pr    || g eg.eg_po
  | Fcoe      coe -> g coe.coe_pre
  | Fpr       pr  -> g pr.pr_args  || g pr.pr_event

(* -------------------------------------------------------------------- *)
let form_forall g f =
  match f.f_node with
  | Fint     _
  | Flocal   _
  | Fpvar    _
  | Fglob    _
  | Fop      _ -> true

  | Fquant   (_ , _ , f1) -> g f1
  | Fif      (f1, f2, f3) -> g f1 && g f2 && g f3
  | Fmatch   (b, fs, _)   -> List.for_all g (b :: fs)
  | Flet     (_, f1, f2)  -> g f1 && g f2
  | Fapp     (e, es)      -> List.for_all g (e :: es)
  | Ftuple   es           -> List.for_all g es
  | Fproj    (e, _)       -> g e

  | FhoareF  hf  -> g hf.hf_pr  && g hf.hf_po
  | FhoareS  hs  -> g hs.hs_pr  && g hs.hs_po
  | FcHoareF  chf -> g chf.chf_pr && g chf.chf_po
  | FcHoareS  chs -> g chs.chs_pr && g chs.chs_po
  | FbdHoareF bhf -> g bhf.bhf_pr && g bhf.bhf_po
  | FbdHoareS bhs -> g bhs.bhs_pr && g bhs.bhs_po
  | FequivF   ef  -> g ef.ef_pr   && g ef.ef_po
  | FequivS   es  -> g es.es_pr   && g es.es_po
  | FeagerF   eg  -> g eg.eg_pr   && g eg.eg_po
  | Fcoe      coe -> g coe.coe_pre
  | Fpr       pr  -> g pr.pr_args && g pr.pr_event
  | FeHoareF  hf  -> g hf.ehf_pr && g hf.ehf_po
  | FeHoareS  hs  -> g hs.ehs_pr && g hs.ehs_po


(* -------------------------------------------------------------------- *)
let f_ops f =
  let aout = ref EcPath.Sp.empty in
  let rec doit f =
    match f.f_node with
    | Fop (p, _) -> aout := Sp.add p !aout
    | _ -> f_iter doit f
  in doit f; !aout

(* -------------------------------------------------------------------- *)
exception DestrError of string

let destr_error e = raise (DestrError e)

(* -------------------------------------------------------------------- *)
let destr_forall1 f =
  match f.f_node with
  | Fquant(Lforall,(x,t)::bd,p) -> x,t,f_forall bd p
  | _ -> destr_error "forall"

let destr_forall f =
  match f.f_node with
  | Fquant(Lforall,bd,p) -> bd, p
  | _ -> destr_error "forall"

let decompose_forall f =
  match f.f_node with
  | Fquant(Lforall,bd,p) -> bd, p
  | _ -> [], f

let destr_lambda f =
  match f.f_node with
  | Fquant(Llambda,bd,p) -> bd, p
  | _ -> destr_error "lambda"

let decompose_lambda f =
  match f.f_node with
  | Fquant(Llambda,bd,p) -> bd, p
  | _ -> [], f

let destr_exists1 f =
  match f.f_node with
  | Fquant(Lexists,(x,t)::bd,p) -> x,t,f_exists bd p
  | _ -> destr_error "exists"

let destr_exists f =
  match f.f_node with
  | Fquant(Lexists,bd,p) -> bd, p
  | _ -> destr_error "exists"

let destr_let f =
  match f.f_node with
  | Flet(lp, e1,e2) -> lp,e1,e2
  | _ -> destr_error "let"

let destr_let1 f =
  match f.f_node with
  | Flet(LSymbol(x,ty), e1,e2) -> x,ty,e1,e2
  | _ -> destr_error "let1"

let destr_equivS f =
  match f.f_node with
  | FequivS es -> es
  | _ -> destr_error "equivS"

let destr_equivF f =
  match f.f_node with
  | FequivF es -> es
  | _ -> destr_error "equivF"

let destr_eagerF f =
  match f.f_node with
  | FeagerF eg -> eg
  | _ -> destr_error "eagerF"

let destr_hoareS f =
  match f.f_node with
  | FhoareS es -> es
  | _ -> destr_error "hoareS"

let destr_hoareF f =
  match f.f_node with
  | FhoareF es -> es
  | _ -> destr_error "hoareF"

let destr_eHoareS f =
  match f.f_node with
  | FeHoareS es -> es
  | _ -> destr_error "eHoareS"

let destr_eHoareF f =
  match f.f_node with
  | FeHoareF es -> es
  | _ -> destr_error "eHoareF"

let destr_cHoareS f =
  match f.f_node with
  | FcHoareS es -> es
  | _ -> destr_error "cHoareS"

let destr_cHoareF f =
  match f.f_node with
  | FcHoareF es -> es
  | _ -> destr_error "cHoareF"

let destr_bdHoareS f =
  match f.f_node with
  | FbdHoareS es -> es
  | _ -> destr_error "bdHoareS"

let destr_bdHoareF f =
  match f.f_node with
  | FbdHoareF es -> es
  | _ -> destr_error "bdHoareF"

let destr_coe f =
  match f.f_node with
  | Fcoe coe -> coe
  | _ -> destr_error "coe"

let destr_pr f =
  match f.f_node with
  | Fpr pr -> pr
  | _ -> destr_error "pr"

let destr_programS side f =
  match side, f.f_node with
  | None  , FhoareS   hs -> (hs.hs_m, hs.hs_s)
  | None  , FcHoareS  chs -> (chs.chs_m, chs.chs_s)
  | None  , FbdHoareS bhs -> (bhs.bhs_m, bhs.bhs_s)
  | Some b, FequivS   es  -> begin
      match b with
      | `Left  -> (es.es_ml, es.es_sl)
      | `Right -> (es.es_mr, es.es_sr)
  end
  | _, _ -> destr_error "programS"

let destr_int f =
  match f.f_node with
  | Fint n -> n

  | Fapp (op, [{f_node = Fint n}]) when f_equal op fop_int_opp ->
      BI.neg n

  | _ -> destr_error "destr_int"

let destr_pvar f =
  match f.f_node with
  | Fpvar(x,m) -> (x,m)
  | _ -> destr_error "destr_pvar"

let destr_glob f =
  match f.f_node with
  | Fglob(m , mem) -> (m, mem)
  | _ -> destr_error "destr_glob"

(* -------------------------------------------------------------------- *)
let is_op_and_sym  p = EcPath.p_equal EcCoreLib.CI_Bool.p_and p
let is_op_and_asym p = EcPath.p_equal EcCoreLib.CI_Bool.p_anda p
let is_op_and_any  p = is_op_and_sym p || is_op_and_asym p
let is_op_or_sym   p = EcPath.p_equal EcCoreLib.CI_Bool.p_or p
let is_op_or_asym  p = EcPath.p_equal EcCoreLib.CI_Bool.p_ora p
let is_op_or_any   p = is_op_or_sym  p || is_op_or_asym  p
let is_op_not      p = EcPath.p_equal EcCoreLib.CI_Bool.p_not p
let is_op_imp      p = EcPath.p_equal EcCoreLib.CI_Bool.p_imp p
let is_op_iff      p = EcPath.p_equal EcCoreLib.CI_Bool.p_iff p
let is_op_eq       p = EcPath.p_equal EcCoreLib.CI_Bool.p_eq  p

(* -------------------------------------------------------------------- *)
let destr_op = function
  { f_node = Fop (op, tys) } -> op, tys | _ -> destr_error "op"

let destr_app = function
  { f_node = Fapp (f, fs) } -> (f, fs) | f -> (f, [])

let destr_op_app f =
  let (fo, args) = destr_app f in destr_op fo, args

let destr_tuple = function
  { f_node = Ftuple fs } -> fs | _ -> destr_error "tuple"

let destr_local = function
  { f_node = Flocal id } -> id | _ -> destr_error "local"

let destr_pvar = function
  { f_node = Fpvar (pv, m) } -> (pv, m) | _ -> destr_error "pvar"

let destr_proj  = function
  { f_node = Fproj (f, i) } -> (f, i) | _ -> destr_error "proj"

let destr_app1 ~name pred form =
  match destr_app form with
  | { f_node = Fop (p, _) }, [f] when pred p -> f
  | _ -> destr_error name

let destr_app2 ~name pred form =
  match destr_app form with
  | { f_node = Fop (p, _) }, [f1; f2] when pred p -> (f1, f2)
  | _ -> destr_error name

let destr_app1_eq ~name p f = destr_app1 ~name (EcPath.p_equal p) f
let destr_app2_eq ~name p f = destr_app2 ~name (EcPath.p_equal p) f

let destr_not = destr_app1 ~name:"not" is_op_not
let destr_and = destr_app2 ~name:"and" is_op_and_any
let destr_or  = destr_app2 ~name:"or"  is_op_or_any
let destr_imp = destr_app2 ~name:"imp" is_op_imp
let destr_iff = destr_app2 ~name:"iff" is_op_iff
let destr_eq  = destr_app2 ~name:"eq"  is_op_eq

let destr_and3 f =
  try
    let c1, (c2, c3) = snd_map destr_and (destr_and f)
    in  (c1, c2, c3)
  with DestrError _ -> raise (DestrError "and3")

let destr_eq_or_iff =
  destr_app2 ~name:"eq-or-iff" (fun p -> is_op_eq p || is_op_iff p)

let destr_or_r form =
  match destr_app form with
  | { f_node = Fop (p, _) }, [f1; f2] when is_op_or_sym  p -> (`Sym , (f1, f2))
  | { f_node = Fop (p, _) }, [f1; f2] when is_op_or_asym p -> (`Asym, (f1, f2))
  | _ -> destr_error "or"

let destr_and_r form =
  match destr_app form with
  | { f_node = Fop (p, _) }, [f1; f2] when is_op_and_sym  p -> (`Sym , (f1, f2))
  | { f_node = Fop (p, _) }, [f1; f2] when is_op_and_asym p -> (`Asym, (f1, f2))
  | _ -> destr_error "and"

let destr_nots form =
  let rec aux b form =
    match try Some (destr_not form) with DestrError _ -> None with
    | None      -> (b, form)
    | Some form -> aux (not b) form
  in aux true form

(* -------------------------------------------------------------------- *)
let is_from_destr dt f =
  try ignore (dt f); true with DestrError _ -> false

let is_true      f = f_equal f f_true
let is_false     f = f_equal f f_false
let is_tuple     f = is_from_destr destr_tuple     f
let is_op        f = is_from_destr destr_op        f
let is_local     f = is_from_destr destr_local     f
let is_pvar      f = is_from_destr destr_pvar      f
let is_glob      f = is_from_destr destr_glob      f
let is_proj      f = is_from_destr destr_proj      f
let is_and       f = is_from_destr destr_and       f
let is_or        f = is_from_destr destr_or        f
let is_not       f = is_from_destr destr_not       f
let is_imp       f = is_from_destr destr_imp       f
let is_iff       f = is_from_destr destr_iff       f
let is_eq        f = is_from_destr destr_eq        f
let is_forall    f = is_from_destr destr_forall1   f
let is_exists    f = is_from_destr destr_exists1   f
let is_lambda    f = is_from_destr destr_lambda    f
let is_let       f = is_from_destr destr_let1      f
let is_equivF    f = is_from_destr destr_equivF    f
let is_equivS    f = is_from_destr destr_equivS    f
let is_eagerF    f = is_from_destr destr_eagerF    f
let is_hoareS    f = is_from_destr destr_hoareS    f
let is_hoareF    f = is_from_destr destr_hoareF    f
let is_eHoareS   f = is_from_destr destr_eHoareS   f
let is_eHoareF   f = is_from_destr destr_eHoareF   f
let is_cHoareS   f = is_from_destr destr_cHoareS   f
let is_cHoareF   f = is_from_destr destr_cHoareF   f
let is_bdHoareS  f = is_from_destr destr_bdHoareS  f
let is_bdHoareF  f = is_from_destr destr_bdHoareF  f
let is_coe       f = is_from_destr destr_coe       f
let is_pr        f = is_from_destr destr_pr        f
let is_eq_or_iff f = (is_eq f) || (is_iff f)

(* -------------------------------------------------------------------- *)
let split_args f =
  match f_node f with
  | Fapp (f, args) -> (f, args)
  | _ -> (f, [])

(* -------------------------------------------------------------------- *)
let split_fun f =
  match f_node f with
  | Fquant (Llambda, bds, body) -> (bds, body)
  | _ -> ([], f)

(* -------------------------------------------------------------------- *)
let quantif_of_equantif (qt : equantif) =
  match qt with
  | `ELambda -> Llambda
  | `EForall -> Lforall
  | `EExists -> Lexists

(* -------------------------------------------------------------------- *)
let equantif_of_quantif (qt : quantif) : equantif =
  match qt with
  | Llambda -> `ELambda
  | Lforall -> `EForall
  | Lexists -> `EExists

(* -------------------------------------------------------------------- *)
let rec form_of_expr mem (e : expr) =
  match e.e_node with
  | Eint n ->
     f_int n

  | Elocal id ->
     f_local id e.e_ty

  | Evar pv ->
     f_pvar pv e.e_ty mem

  | Eop (op, tys) ->
     f_op op tys e.e_ty

  | Eapp (ef, es) ->
     f_app (form_of_expr mem ef) (List.map (form_of_expr mem) es) e.e_ty

  | Elet (lpt, e1, e2) ->
     f_let lpt (form_of_expr mem e1) (form_of_expr mem e2)

  | Etuple es ->
     f_tuple (List.map (form_of_expr mem) es)

  | Eproj (e1, i) ->
     f_proj (form_of_expr mem e1) i e.e_ty

  | Eif (e1, e2, e3) ->
     let e1 = form_of_expr mem e1 in
     let e2 = form_of_expr mem e2 in
     let e3 = form_of_expr mem e3 in
     f_if e1 e2 e3

  | Ematch (b, fs, ty) ->
     let b'  = form_of_expr mem b in
     let fs' = List.map (form_of_expr mem) fs in
     f_match b' fs' ty

  | Equant (qt, b, e) ->
     let b = List.map (fun (x, ty) -> (x, GTty ty)) b in
     let e = form_of_expr mem e in
     f_quant (quantif_of_equantif qt) b e


(* -------------------------------------------------------------------- *)
exception CannotTranslate

let expr_of_form mh f =
  let rec aux fp =
    match fp.f_node with
    | Fint   z -> e_int z
    | Flocal x -> e_local x fp.f_ty

    | Fop  (p, tys) -> e_op p tys fp.f_ty
    | Fapp (f, fs)  -> e_app (aux f) (List.map aux fs) fp.f_ty
    | Ftuple fs     -> e_tuple (List.map aux fs)
    | Fproj  (f, i) -> e_proj (aux f) i fp.f_ty

    | Fif (c, f1, f2) ->
      e_if (aux c) (aux f1) (aux f2)

    | Fmatch (c, bs, ty) ->
      e_match (aux c) (List.map aux bs) ty

    | Flet (lp, f1, f2) ->
      e_let lp (aux f1) (aux f2)

    | Fquant (kd, bds, f) ->
      e_quantif (equantif_of_quantif kd) (List.map auxbd bds) (aux f)

    | Fpvar (pv, m) ->
      if EcIdent.id_equal m mh
      then e_var pv fp.f_ty
      else raise CannotTranslate

    | Fcoe      _
    | Fglob     _
    | FhoareF   _ | FhoareS   _
    | FcHoareF  _ | FcHoareS  _
    | FeHoareF  _ | FeHoareS  _
    | FbdHoareF _ | FbdHoareS _
    | FequivF   _ | FequivS   _
    | FeagerF   _ | Fpr       _ -> raise CannotTranslate

  and auxbd ((x, bd) : binding) =
    match bd with
    | GTty ty -> (x, ty)
    | _ -> raise CannotTranslate

  in aux f

(* -------------------------------------------------------------------- *)
(* A predicate on memory: λ mem. -> pred *)
type mem_pr = EcMemory.memory * form

(* -------------------------------------------------------------------- *)
type f_subst = {
  fs_freshen  : bool; (* true means freshen locals *)
  fs_loc      : form Mid.t;
  fs_esloc    : expr Mid.t;
  fs_ty       : ty_subst;
  fs_mem      : EcIdent.t Mid.t;
  fs_modglob  : (EcIdent.t -> form) Mid.t; (* Mappings between abstract modules and their globals *)
  fs_memtype  : EcMemory.memtype option; (* Only substituted in Fcoe *)
  fs_mempred  : mem_pr Mid.t;  (* For predicates over memories,
                                 only substituted in Fcoe *)
}

(* -------------------------------------------------------------------- *)
module Fsubst = struct

  let f_subst_id = {
    fs_freshen  = false;
    fs_loc      = Mid.empty;
    fs_esloc    = Mid.empty;
    fs_ty       = ty_subst_id;
    fs_mem      = Mid.empty;
    fs_modglob  = Mid.empty;
    fs_memtype  = None;
    fs_mempred  = Mid.empty;
  }

  let is_subst_id s =
       s.fs_freshen = false
    && is_ty_subst_id s.fs_ty
    && Mid.is_empty   s.fs_loc
    && Mid.is_empty   s.fs_mem
    && Mid.is_empty   s.fs_modglob
    && Mid.is_empty   s.fs_esloc
    && s.fs_memtype = None

  let f_subst_init ?freshen ?sty ?esloc ?mt ?mempred () =
    let sty = odfl ty_subst_id sty in
    { f_subst_id
        with fs_freshen  = odfl false freshen;
             fs_ty       = sty;
             fs_esloc    = odfl Mid.empty esloc;
             fs_mempred  = odfl Mid.empty mempred;
             fs_memtype  = mt; }

  (* ------------------------------------------------------------------ *)
  let f_bind_local s x t =
    let merger o = assert (o = None); Some t in
      { s with fs_loc = Mid.change merger x s.fs_loc }

  let f_bind_mem s m1 m2 =
    let merger o = assert (o = None); Some m2 in
      { s with fs_mem = Mid.change merger m1 s.fs_mem }

  let f_rebind_mem s m1 m2 =
    let merger _ = Some m2 in
    { s with fs_mem = Mid.change merger m1 s.fs_mem }

  let f_bind_absmod s m1 m2 =
    let merger o = assert (o = None); Some m2 in
    let sty = { s.fs_ty with ts_absmod = Mid.change merger m1 s.fs_ty.ts_absmod } in
    let sty = { sty with ts_cmod = Mid.add m1 (EcPath.mident m2) s.fs_ty.ts_cmod } in
    { s with fs_ty = sty }

  let f_bind_cmod s m mp =
    let merger o = assert (o = None); Some mp in
    let sty = { s.fs_ty with ts_cmod = Mid.change merger m s.fs_ty.ts_cmod } in
    { s with fs_ty = sty }

  let f_bind_mod s x mp norm_mod =
    match EcPath.mget_ident_opt mp with
    | Some id ->
         f_bind_absmod s x id
    | None ->
       let nm_ty = (norm_mod mhr).f_ty in
       let s = f_bind_cmod s x mp in
       let sty = { s.fs_ty with ts_modtglob = Mid.add x nm_ty s.fs_ty.ts_modtglob } in
       { s with fs_ty = sty; fs_modglob = Mid.add x norm_mod s.fs_modglob }

  let f_bind_rename s xfrom xto ty =
    let xf = f_local xto ty in
    let xe = e_local xto ty in
    let s  = f_bind_local s xfrom xf in

    let merger o = assert (o = None); Some xe in
    { s with fs_esloc = Mid.change merger xfrom s.fs_esloc }

  (* ------------------------------------------------------------------ *)
  let f_rem_local s x =
    { s with fs_loc = Mid.remove x s.fs_loc;
             fs_esloc = Mid.remove x s.fs_esloc; }

  let f_rem_mem s m =
    { s with fs_mem = Mid.remove m s.fs_mem }

  let f_rem_mod s x =
    { s with
        fs_ty = { (s.fs_ty) with
          ts_absmod = Mid.remove x s.fs_ty.ts_absmod;
          ts_modtglob = Mid.remove x s.fs_ty.ts_modtglob;
          ts_cmod = Mid.remove x s.fs_ty.ts_cmod; };
        fs_modglob = Mid.remove x s.fs_modglob; }

  (* ------------------------------------------------------------------ *)
  let add_local s (x,t as xt) =
    let x' = if s.fs_freshen then EcIdent.fresh x else x in
    let t' = ty_subst s.fs_ty t in
      if   x == x' && t == t'
      then (s, xt)
      else (f_bind_rename s x x' t'), (x',t')

  let add_locals = List.Smart.map_fold add_local

  let subst_lpattern (s: f_subst) (lp:lpattern) =
    match lp with
    | LSymbol x ->
        let (s, x') = add_local s x in
          if x == x' then (s, lp) else (s, LSymbol x')

    | LTuple xs ->
        let (s, xs') = add_locals s xs in
          if xs == xs' then (s, lp) else (s, LTuple xs')

    | LRecord (p, xs) ->
        let (s, xs') =
          List.Smart.map_fold
            (fun s ((x, t) as xt) ->
              match x with
              | None ->
                  let t' = ty_subst s.fs_ty t in
                    if t == t' then (s, xt) else (s, (x, t'))
              | Some x ->
                  let (s, (x', t')) = add_local s (x, t) in
                    if   x == x' && t == t'
                    then (s, xt)
                    else (s, (Some x', t')))
            s xs
        in
          if xs == xs' then (s, lp) else (s, LRecord (p, xs'))

  (* ------------------------------------------------------------------ *)
  let subst_xpath s f =
    EcPath.x_subst_abs s.fs_ty.ts_cmod f

  let subst_stmt s c =
    let es =
      e_subst_init s.fs_freshen s.fs_ty s.fs_esloc
    in EcCoreModules.s_subst es c

  let subst_e s e =
    let es  = e_subst_init s.fs_freshen s.fs_ty s.fs_esloc in
    EcTypes.e_subst es e

  let subst_me s me =
    EcMemory.me_subst s.fs_mem (ty_subst s.fs_ty) me

  let subst_m s m = Mid.find_def m m s.fs_mem

  let subst_ty s ty = ty_subst s.fs_ty ty

  (* ------------------------------------------------------------------ *)
  let rec f_subst ~tx s fp =
    tx fp (match fp.f_node with
    | Fquant (q, b, f) ->
        let s, b' = add_bindings ~tx s b in
        let f'    = f_subst ~tx s f in
          f_quant q b' f'

    | Flet (lp, f1, f2) ->
        let f1'    = f_subst ~tx s f1 in
        let s, lp' = subst_lpattern s lp in
        let f2'    = f_subst ~tx s f2 in
          f_let lp' f1' f2'

    | Flocal id -> begin
      match Mid.find_opt id s.fs_loc with
      | Some f -> f
      | None ->
          let ty' = ty_subst s.fs_ty fp.f_ty in
          f_local id ty'
    end

    | Fop (p, tys) ->
        let ty'  = ty_subst s.fs_ty fp.f_ty in
        let tys' = List.Smart.map (ty_subst s.fs_ty) tys in
        f_op p tys' ty'

    | Fpvar (pv, m) ->
        let pv' = pv_subst (subst_xpath s) pv in
        let m'  = Mid.find_def m m s.fs_mem in
        let ty' = ty_subst s.fs_ty fp.f_ty in
        f_pvar pv' ty' m'

    | Fglob (mid, m) ->
        let m'  = Mid.find_def m m s.fs_mem in
        let mid = Mid.find_def mid mid s.fs_ty.ts_absmod in
        begin
          (* Have we computed the globals for this module *)
          match Mid.find_opt mid s.fs_modglob with
          | None -> f_glob mid m'
          | Some f -> f m'
        end

    | FhoareF hf ->
      let pr', po' =
        let s   = f_rem_mem s mhr in
        let pr' = f_subst ~tx s hf.hf_pr in
        let po' = f_subst ~tx s hf.hf_po in
        (pr', po') in
      let mp' = subst_xpath s hf.hf_f in

      f_hoareF pr' mp' po'

    | FhoareS hs ->
        assert (not (Mid.mem (fst hs.hs_m) s.fs_mem));
        let es  = e_subst_init s.fs_freshen s.fs_ty s.fs_esloc in
        let pr' = f_subst ~tx s hs.hs_pr in
        let po' = f_subst ~tx s hs.hs_po in
        let st' = EcCoreModules.s_subst es hs.hs_s in
        let me' = EcMemory.me_subst s.fs_mem (ty_subst s.fs_ty) hs.hs_m in

        f_hoareS me' pr' st' po'


    | FeHoareF hf ->
        assert (not (Mid.mem mhr s.fs_mem) && not (Mid.mem mhr s.fs_mem));
        let ehf_pr  = f_subst ~tx s hf.ehf_pr in
        let ehf_po  = f_subst ~tx s hf.ehf_po in
        let ehf_f  = subst_xpath s hf.ehf_f in
        f_eHoareF ehf_pr ehf_f ehf_po

    | FeHoareS hs ->
        assert (not (Mid.mem (fst hs.ehs_m) s.fs_mem));
        let es  = e_subst_init s.fs_freshen s.fs_ty s.fs_esloc in
        let ehs_pr  = f_subst ~tx s hs.ehs_pr in
        let ehs_po  = f_subst ~tx s hs.ehs_po in
        let ehs_s  = EcCoreModules.s_subst es hs.ehs_s in
        let ehs_m = EcMemory.me_subst s.fs_mem (ty_subst s.fs_ty) hs.ehs_m in
        f_eHoareS ehs_m ehs_pr ehs_s ehs_po

    | FcHoareF chf ->
      assert (not (Mid.mem mhr s.fs_mem));
      let pr' = f_subst ~tx s chf.chf_pr in
      let po' = f_subst ~tx s chf.chf_po in
      let mp' = subst_xpath s chf.chf_f in
      let c'  = cost_subst ~tx s chf.chf_co in

      f_cHoareF pr' mp' po' c'

    | FcHoareS chs ->
      assert (not (Mid.mem (fst chs.chs_m) s.fs_mem));
      let es  = e_subst_init s.fs_freshen s.fs_ty s.fs_esloc in
      let pr' = f_subst ~tx s chs.chs_pr in
      let po' = f_subst ~tx s chs.chs_po in
      let st' = EcCoreModules.s_subst es chs.chs_s in
      let me' = EcMemory.me_subst s.fs_mem (ty_subst s.fs_ty) chs.chs_m in
      let c'  = cost_subst ~tx s chs.chs_co in

      f_cHoareS me' pr' st' po' c'

    | FbdHoareF bhf ->
      let pr', po', bd' =
        let s = f_rem_mem s mhr in
        let pr' = f_subst ~tx s bhf.bhf_pr in
        let po' = f_subst ~tx s bhf.bhf_po in
        let bd' = f_subst ~tx s bhf.bhf_bd in
        (pr', po', bd') in
      let mp' = subst_xpath s bhf.bhf_f in

      f_bdHoareF_r { bhf with bhf_pr = pr'; bhf_po = po';
                              bhf_f  = mp'; bhf_bd = bd'; }

    | FbdHoareS bhs ->
      assert (not (Mid.mem (fst bhs.bhs_m) s.fs_mem));
      let es  = e_subst_init s.fs_freshen s.fs_ty s.fs_esloc in
      let pr' = f_subst ~tx s bhs.bhs_pr in
      let po' = f_subst ~tx s bhs.bhs_po in
      let st' = EcCoreModules.s_subst es bhs.bhs_s in
      let me' = EcMemory.me_subst s.fs_mem (ty_subst s.fs_ty) bhs.bhs_m in
      let bd' = f_subst ~tx s bhs.bhs_bd in

      f_bdHoareS_r { bhs with bhs_pr = pr'; bhs_po = po'; bhs_s = st';
                              bhs_bd = bd'; bhs_m  = me'; }

    | FequivF ef ->
      let pr', po' =
        let s = f_rem_mem s mleft in
        let s = f_rem_mem s mright in
        let pr' = f_subst ~tx s ef.ef_pr in
        let po' = f_subst ~tx s ef.ef_po in
        (pr', po') in
      let fl' = subst_xpath s ef.ef_fl in
      let fr' = subst_xpath s ef.ef_fr in

      f_equivF pr' fl' fr' po'

    | FequivS eqs ->
      assert (not (Mid.mem (fst eqs.es_ml) s.fs_mem) &&
                not (Mid.mem (fst eqs.es_mr) s.fs_mem));
      let es = e_subst_init s.fs_freshen s.fs_ty s.fs_esloc in
      let s_subst = EcCoreModules.s_subst es in
      let pr' = f_subst ~tx s eqs.es_pr in
      let po' = f_subst ~tx s eqs.es_po in
      let sl' = s_subst eqs.es_sl in
      let sr' = s_subst eqs.es_sr in
      let ml' = EcMemory.me_subst s.fs_mem (ty_subst s.fs_ty) eqs.es_ml in
      let mr' = EcMemory.me_subst s.fs_mem (ty_subst s.fs_ty) eqs.es_mr in

      f_equivS ml' mr' pr' sl' sr' po'

    | FeagerF eg ->
      let pr', po' =
        let s = f_rem_mem s mleft in
        let s = f_rem_mem s mright in
        let pr' = f_subst ~tx s eg.eg_pr in
        let po' = f_subst ~tx s eg.eg_po in
        (pr', po') in
      let fl' = subst_xpath s eg.eg_fl in
      let fr' = subst_xpath s eg.eg_fr in

      let es = e_subst_init s.fs_freshen s.fs_ty s.fs_esloc in
      let s_subst = EcCoreModules.s_subst es in
      let sl' = s_subst eg.eg_sl in
      let sr' = s_subst eg.eg_sr in

      f_eagerF pr' sl' fl' fr' sr' po'

    | Fcoe coe ->
      (* We freshen the binded memory. *)
      let m = fst coe.coe_mem in
      let m' = EcIdent.fresh m in
      let s = f_rebind_mem s m m' in

      (* We bind the memory of all memory predicates with the fresh memory
         we just created, and add them as local variable substitutions. *)
      let s = Mid.fold (fun id (pmem,p) s ->
          let fs_mem = f_bind_mem f_subst_id pmem m' in
          let p = f_subst ~tx:(fun _ f -> f) fs_mem p in
          f_bind_local s id p
        ) s.fs_mempred { s with fs_mempred = Mid.empty; } in


      (* Then we substitute *)
      let es  = e_subst_init s.fs_freshen s.fs_ty s.fs_esloc in
      let pr' = f_subst ~tx s coe.coe_pre in
      let me' = EcMemory.me_subst s.fs_mem (ty_subst s.fs_ty) coe.coe_mem in
      let e' = EcTypes.e_subst es coe.coe_e in

      (* If necessary, we substitute the memtype. *)
      let me' =
        if EcMemory.is_schema (snd me') && s.fs_memtype <> None
        then (fst me', oget s.fs_memtype)
        else me' in

      f_coe pr' me' e'

    | Fpr pr ->
      let pr_mem   = Mid.find_def pr.pr_mem pr.pr_mem s.fs_mem in
      let pr_fun   = subst_xpath s pr.pr_fun in
      let pr_args  = f_subst ~tx s pr.pr_args in
      let s = f_rem_mem s mhr in
      let pr_event = f_subst ~tx s pr.pr_event in

      f_pr pr_mem pr_fun pr_args pr_event

    | _ ->
      f_map (ty_subst s.fs_ty) (f_subst ~tx s) fp)

  and f_subst_op ~tx freshen fty tys args (tyids, e) =
    (* FIXME: factor this out *)
    (* FIXME: is [mhr] good as a default? *)

    let e =
      let sty = Tvar.init tyids tys in
      let sty = { ty_subst_id with ts_v = sty} in
      let sty = { e_subst_id with es_freshen = freshen; es_ty = sty } in
        e_subst sty e
    in

    let (sag, args, e) =
      match e.e_node with
      | Equant (`ELambda, largs, lbody) when args <> [] ->
          let largs1, largs2 = List.takedrop (List.length args  ) largs in
          let  args1,  args2 = List.takedrop (List.length largs1)  args in
            (Mid.of_list (List.combine (List.map fst largs1) args1),
             args2, e_lam largs2 lbody)

      | _ -> (Mid.of_list [], args, e)
    in

    let sag = { f_subst_id with fs_loc = sag } in
      f_app (f_subst ~tx sag (form_of_expr mhr e)) args fty

  and f_subst_pd ~tx fty tys args (tyids, f) =
    (* FIXME: factor this out *)
    (* FIXME: is fd_freshen value correct? *)

    let f =
      let sty = Tvar.init tyids tys in
      let sty = { ty_subst_id with ts_v = sty} in
      let sty = { f_subst_id with fs_freshen = true; fs_ty = sty } in
      f_subst ~tx sty f
    in

    let (sag, args, f) =
      match f.f_node with
      | Fquant (Llambda, largs, lbody) when args <> [] ->
          let largs1, largs2 = List.takedrop (List.length args  ) largs in
          let  args1,  args2 = List.takedrop (List.length largs1)  args in
            (Mid.of_list (List.combine (List.map fst largs1) args1),
             args2, f_lambda largs2 lbody)

      | _ -> (Mid.of_list [], args, f)
    in

    let sag = { f_subst_id with fs_loc = sag } in
    f_app (f_subst ~tx sag f) args fty

  and subst_oi ~(tx : form -> form -> form) (s : f_subst) (oi : PreOI.t) =
    let costs = match PreOI.costs oi with
      | `Unbounded -> `Unbounded
      | `Bounded (self,calls) ->
        let calls = EcPath.Mx.fold (fun x a calls ->
            EcPath.Mx.change
              (fun old -> assert (old = None); Some (f_subst ~tx s a))
              (subst_xpath s x)
              calls
          ) calls EcPath.Mx.empty in
        let self = f_subst ~tx s self in
        `Bounded (self,calls) in

    PreOI.mk
      (List.map (subst_xpath s) (PreOI.allowed oi))
      costs

  and mr_subst ~tx s mr : mod_restr =
    let sx = subst_xpath s in
    let sm = EcPath.m_subst_abs s.fs_ty.ts_cmod in
    { mr_xpaths = ur_app (fun s -> Sx.fold (fun m rx ->
          Sx.add (sx m) rx) s Sx.empty) mr.mr_xpaths;
      mr_mpaths = ur_app (fun s -> Sm.fold (fun m r ->
          Sm.add (sm m) r) s Sm.empty) mr.mr_mpaths;
      mr_oinfos = EcSymbols.Msym.map (subst_oi ~tx s) mr.mr_oinfos;
    }

  and subst_mty ~tx s mty =
    let sm = EcPath.m_subst_abs s.fs_ty.ts_cmod in

    let mt_params = List.map (snd_map (subst_mty ~tx s)) mty.mt_params in
    let mt_name   = mty.mt_name in
    let mt_args   = List.map sm mty.mt_args in
    let mt_restr  = mr_subst ~tx s mty.mt_restr in
    { mt_params; mt_name; mt_args; mt_restr; }

  and subst_gty ~tx s gty =
    if is_subst_id s then gty else

    match gty with
    | GTty ty ->
        let ty' = ty_subst s.fs_ty ty in
        if ty == ty' then gty else GTty ty'

    | GTmodty p ->
        let p' = subst_mty ~tx s p in

        if   p == p'
        then gty
        else GTmodty p'

    | GTmem mt ->
        let mt' = EcMemory.mt_subst (ty_subst s.fs_ty) mt in
        if mt == mt' then gty else GTmem mt'

  and add_binding ~tx s (x, gty as xt) =
    let gty' = subst_gty ~tx s gty in
    let x'   = if s.fs_freshen then EcIdent.fresh x else x in

    if x == x' && gty == gty' then
      let s = match gty with
        | GTty    _ -> f_rem_local s x
        | GTmodty _ -> f_rem_mod   s x
        | GTmem   _ -> f_rem_mem   s x
      in
        (s, xt)
    else
      let s = match gty' with
        | GTty   ty -> f_bind_rename s x x' ty
        | GTmodty _ -> f_bind_absmod s x x'
        | GTmem   _ -> f_bind_mem s x x'
      in
        (s, (x', gty'))

  and add_bindings ~tx = List.map_fold (add_binding ~tx)

  (* When substituting a abstract module (i.e. a mident) by a concrete one,
     we move the module cost from [c_calls] to [c_self]. *)
  and cost_subst ~tx s cost =
    let c_self = f_subst ~tx s cost.c_self
    and self', c_calls = EcPath.Mx.fold (fun x cb (self',calls) ->
        let x' = subst_xpath s x in
        let cb_cost'   = f_subst ~tx s cb.cb_cost in
        let cb_called' = f_subst ~tx s cb.cb_called in
        match x'.x_top.m_top with
        | `Local _ ->
          let cb' = { cb_cost   = cb_cost';
                      cb_called = cb_called'; } in
          ( self',
            EcPath.Mx.change
              (fun old -> assert (old  = None); Some cb')
              x' calls )
        | `Concrete _ ->
          (* TODO: A: better simplification*)
          ( f_xadd_simpl self' (f_xmuli_simpl cb_called' cb_cost'), calls)
      ) cost.c_calls (f_x0, EcPath.Mx.empty) in

    let c_self = f_xadd_simpl c_self self' in
    cost_r c_self c_calls

  (* ------------------------------------------------------------------ *)
  let add_binding  = add_binding ~tx:(fun _ f -> f)
  let add_bindings = add_bindings ~tx:(fun _ f -> f)

  (* ------------------------------------------------------------------ *)
  let f_subst ?(tx = fun _ f -> f) s =
    if is_subst_id s then identity else f_subst ~tx s

  let subst_gty = subst_gty ~tx:(fun _ f -> f)
  let subst_mty = subst_mty ~tx:(fun _ f -> f)
  let subst_oi  = subst_oi ~tx:(fun _ f -> f)

  let f_subst_local x t =
    let s = f_bind_local f_subst_id x t in
    fun f -> if Mid.mem x f.f_fv then f_subst s f else f

  let f_subst_mem m1 m2 =
    let s = f_bind_mem f_subst_id m1 m2 in
    fun f -> if Mid.mem m1 f.f_fv then f_subst s f else f

  (* ------------------------------------------------------------------ *)
  let fty_subst sty =
    { f_subst_id with fs_ty = sty }

  let mapty sty =
    f_subst (fty_subst sty)

  (* ------------------------------------------------------------------ *)
  let init_subst_tvar ?es_loc s =
    let sty = { ty_subst_id with ts_v = s } in
    { f_subst_id with
      fs_freshen = true;
      fs_ty = sty;
      fs_esloc = odfl Mid.empty es_loc; }

  let subst_tvar ?es_loc s =
    f_subst (init_subst_tvar ?es_loc s)
end

(* -------------------------------------------------------------------- *)
let can_subst f =
  match f.f_node with
  | Fint _ | Flocal _ | Fpvar _ | Fop _ -> true
  | _ -> false

(* -------------------------------------------------------------------- *)
type core_op = [
  | `True
  | `False
  | `Not
  | `And of [`Asym | `Sym]
  | `Or  of [`Asym | `Sym]
  | `Imp
  | `Iff
  | `Eq
]

let core_ops =
  let core_ops =
    [EcCoreLib.CI_Bool.p_true    , `True     ;
     EcCoreLib.CI_Bool.p_false   , `False    ;
     EcCoreLib.CI_Bool.p_not     , `Not      ;
     EcCoreLib.CI_Bool.p_anda    , `And `Asym;
     EcCoreLib.CI_Bool.p_and     , `And `Sym ;
     EcCoreLib.CI_Bool.p_ora     , `Or  `Asym;
     EcCoreLib.CI_Bool.p_or      , `Or  `Sym ;
     EcCoreLib.CI_Bool.p_imp     , `Imp      ;
     EcCoreLib.CI_Bool.p_iff     , `Iff      ;
     EcCoreLib.CI_Bool.p_eq      , `Eq       ; ]
  in

  let tbl = EcPath.Hp.create 11 in
    List.iter (fun (p, k) -> EcPath.Hp.add tbl p k) core_ops;
    tbl

let core_op_kind (p : EcPath.path) =
  EcPath.Hp.find_opt core_ops p
