(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV
open EcSubst
open EcReduction

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let conseq_cond_ss pre post spre spost =
  map_ss_inv2 f_imp pre spre, map_ss_inv2 f_imp spost post

let conseq_cond_ts pre post spre spost =
  map_ts_inv2 f_imp pre spre, map_ts_inv2 f_imp spost post

(*
{ sF } c { sf }  sF <= F  f <= sf
--------------------------------------------------------------------
{ F } c { f }
 *)
let conseq_econd pre post spre spost =
  let spre = ss_inv_rebind spre pre.m in
  let spost = ss_inv_rebind spost post.m in
  map_ss_inv2 f_xreal_le spre pre, map_ss_inv2 f_xreal_le post spost

let bd_goal_r fcmp fbd cmp bd =
  match fcmp, cmp with
  | FHle, (FHle | FHeq) -> Some (map_ss_inv2 f_real_le bd fbd)
  | FHge, (FHge | FHeq) -> Some (map_ss_inv2 f_real_le fbd bd)
  | FHeq, FHeq          -> Some (map_ss_inv2 f_eq bd fbd)
  | FHeq, FHge          -> Some (map_ss_inv2 f_and 
          (map_ss_inv1 ((EcUtils.flip f_eq) f_r1) fbd) 
          (map_ss_inv1 ((EcUtils.flip f_eq) f_r1) bd))
  | FHeq, FHle          -> Some (map_ss_inv2 f_and 
          (map_ss_inv1 ((EcUtils.flip f_eq) f_r0) fbd) 
          (map_ss_inv1 ((EcUtils.flip f_eq) f_r0) bd))
  | _   , _             -> None

let bd_goal tc fcmp fbd cmp bd =
  match bd_goal_r fcmp fbd cmp bd with
  | None    ->
    let ppe = EcPrinting.PPEnv.ofenv (FApi.tc1_env tc) in
    tc_error !!tc
      "do not know how to change phoare[...]%s %a into phoare[...]%s %a"
      (EcPrinting.string_of_hcmp fcmp) (EcPrinting.pp_form ppe) fbd.inv
      (EcPrinting.string_of_hcmp cmp) (EcPrinting.pp_form ppe) bd.inv
  | Some fp -> fp

(* -------------------------------------------------------------------- *)
let t_hoareF_conseq pre post tc =
  let env = FApi.tc1_env tc in
  let hf  = tc1_as_hoareF tc in
  let pre = ss_inv_rebind pre hf.hf_m in
  let post = ss_inv_rebind post hf.hf_m in
  let mpr,mpo = EcEnv.Fun.hoareF_memenv hf.hf_m hf.hf_f env in
  let cond1, cond2 = conseq_cond_ss (hf_pr hf) (hf_po hf) pre post in
  let concl1 = f_forall_mems_ss_inv mpr cond1 in
  let concl2 = f_forall_mems_ss_inv mpo cond2 in
  let concl3 = f_hoareF pre hf.hf_f post in
  FApi.xmutate1 tc `Conseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_hoareS_conseq pre post tc =
  let hs = tc1_as_hoareS tc in
  let pre = ss_inv_rebind pre (fst hs.hs_m) in
  let post = ss_inv_rebind post (fst hs.hs_m) in
  let cond1, cond2 = conseq_cond_ss (hs_pr hs) (hs_po hs) pre post in
  let concl1 = f_forall_mems_ss_inv hs.hs_m cond1 in
  let concl2 = f_forall_mems_ss_inv hs.hs_m cond2 in
  let concl3 = f_hoareS (snd hs.hs_m) pre hs.hs_s post in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_ehoareF_conseq pre post tc =
  let env = FApi.tc1_env tc in
  let hf  = tc1_as_ehoareF tc in
  let mpr,mpo = EcEnv.Fun.hoareF_memenv hf.ehf_m hf.ehf_f env in
  let cond1, cond2 =
    conseq_econd (ehf_pr hf) (ehf_po hf) pre post in
  let concl1 = f_forall_mems_ss_inv mpr cond1 in
  let concl2 = f_forall_mems_ss_inv mpo cond2 in
  let concl3 = f_eHoareF pre hf.ehf_f post in
  FApi.xmutate1 tc `Conseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_ehoareS_conseq pre post tc =
  let hs = tc1_as_ehoareS tc in
  let cond1, cond2 =
    conseq_econd (ehs_pr hs) (ehs_po hs) pre post in
  let concl1 = f_forall_mems_ss_inv hs.ehs_m cond1 in
  let concl2 = f_forall_mems_ss_inv hs.ehs_m cond2 in
  let concl3 = f_eHoareS (snd hs.ehs_m) pre hs.ehs_s post in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)

let bdHoare_conseq_conds cmp pr po new_pr new_po =
  let cond1, cond2 = conseq_cond_ss pr po new_pr new_po in
  let cond2 = match cmp with
    | FHle -> map_ss_inv2 f_imp po new_po
    | FHeq -> map_ss_inv2 f_iff po new_po
    | FHge -> cond2
  in
  cond1, cond2

(* -------------------------------------------------------------------- *)

let t_bdHoareF_conseq pre post tc =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in
  let mpr,mpo = EcEnv.Fun.hoareF_memenv bhf.bhf_m bhf.bhf_f env in
  let pre = ss_inv_rebind pre bhf.bhf_m in
  let post = ss_inv_rebind post bhf.bhf_m in
  let cond1, cond2 =
    bdHoare_conseq_conds bhf.bhf_cmp (bhf_pr bhf) (bhf_po bhf) pre post in
  let concl1 = f_forall_mems_ss_inv mpr cond1 in
  let concl2 = f_forall_mems_ss_inv mpo cond2 in
  let concl3 = f_bdHoareF pre bhf.bhf_f post bhf.bhf_cmp (bhf_bd bhf) in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_bdHoareS_conseq pre post tc =
  let bhs = tc1_as_bdhoareS tc in
  let pre = ss_inv_rebind pre (fst bhs.bhs_m) in
  let post = ss_inv_rebind post (fst bhs.bhs_m) in
  let cond1, cond2 =
    bdHoare_conseq_conds bhs.bhs_cmp (bhs_pr bhs) (bhs_po bhs) pre post in
  let concl1 = f_forall_mems_ss_inv bhs.bhs_m cond1 in
  let concl2 = f_forall_mems_ss_inv bhs.bhs_m cond2 in
  let concl3 = f_bdHoareS (snd bhs.bhs_m) pre bhs.bhs_s post bhs.bhs_cmp (bhs_bd bhs) in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_bdHoareF_conseq_bd cmp bd tc =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in
  let bd = ss_inv_rebind bd bhf.bhf_m in
  let mpr,_ = EcEnv.Fun.hoareF_memenv bhf.bhf_m bhf.bhf_f env in
  let bd_goal =  bd_goal tc bhf.bhf_cmp (bhf_bd bhf) cmp bd in
  let concl = f_bdHoareF (bhf_pr bhf) bhf.bhf_f (bhf_po bhf) cmp bd in
  let goal = map_ss_inv2 f_imp (bhf_pr bhf) bd_goal in
  let bd_goal = f_forall_mems_ss_inv mpr goal in
  FApi.xmutate1 tc `HlConseq [bd_goal; concl]

(* -------------------------------------------------------------------- *)
let t_bdHoareS_conseq_bd cmp bd tc =
  let bhs = tc1_as_bdhoareS tc in
  let bd = ss_inv_rebind bd (fst bhs.bhs_m) in
  let bd_goal = bd_goal tc bhs.bhs_cmp (bhs_bd bhs) cmp bd in
  let concl = f_bdHoareS (snd bhs.bhs_m) (bhs_pr bhs) bhs.bhs_s (bhs_po bhs) cmp bd in
  let imp = map_ss_inv2 f_imp (bhs_pr bhs) bd_goal in
  let bd_goal = f_forall_mems_ss_inv bhs.bhs_m imp in
  FApi.xmutate1 tc `HlConseq [bd_goal; concl]

(* -------------------------------------------------------------------- *)
let t_equivF_conseq pre post tc =
  let env = FApi.tc1_env tc in
  let ef  = tc1_as_equivF tc in
  let (mprl,mprr), (mpol,mpor) =
    EcEnv.Fun.equivF_memenv ef.ef_ml ef.ef_mr ef.ef_fl ef.ef_fr env in
  let pre = ts_inv_rebind pre ef.ef_ml ef.ef_mr in
  let post = ts_inv_rebind post ef.ef_ml ef.ef_mr in
  let cond1, cond2 = conseq_cond_ts (ef_pr ef) (ef_po ef) pre post in
  let concl1 = f_forall_mems_ts_inv mprl mprr cond1 in
  let concl2 = f_forall_mems_ts_inv mpol mpor cond2 in
  let concl3 = f_equivF pre ef.ef_fl ef.ef_fr post in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_eagerF_conseq pre post tc =
  let env = FApi.tc1_env tc in
  let eg = tc1_as_eagerF tc in
  let (mprl,mprr), (mpol,mpor) =
    EcEnv.Fun.equivF_memenv eg.eg_ml eg.eg_mr eg.eg_fl eg.eg_fr env in
  let pre = ts_inv_rebind pre eg.eg_ml eg.eg_mr in
  let post = ts_inv_rebind post eg.eg_ml eg.eg_mr in
  let cond1, cond2 = conseq_cond_ts (eg_pr eg) (eg_po eg) pre post in
  let concl1 = f_forall_mems_ts_inv mprl mprr cond1 in
  let concl2 = f_forall_mems_ts_inv mpol mpor cond2 in
  let concl3 = f_eagerF pre eg.eg_sl eg.eg_fl eg.eg_fr eg.eg_sr post in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_equivS_conseq pre post tc =
  let es = tc1_as_equivS tc in
  let pre = ts_inv_rebind pre (fst es.es_ml) (fst es.es_mr) in
  let post = ts_inv_rebind post (fst es.es_ml) (fst es.es_mr) in
  let cond1, cond2 = conseq_cond_ts (es_pr es) (es_po es) pre post in
  let concl1 = f_forall_mems_ts_inv es.es_ml es.es_mr cond1 in
  let concl2 = f_forall_mems_ts_inv es.es_ml es.es_mr cond2 in
  let concl3 = f_equivS (snd es.es_ml) (snd es.es_mr) pre es.es_sl es.es_sr post in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_conseq pre post tc =
  match (FApi.tc1_goal tc).f_node, pre, post with
  | FhoareF _,   Inv_ss pre, Inv_ss post -> t_hoareF_conseq pre post tc
  | FhoareS _,   Inv_ss pre, Inv_ss post -> t_hoareS_conseq pre post tc
  | FbdHoareF _, Inv_ss pre, Inv_ss post -> t_bdHoareF_conseq pre post tc
  | FbdHoareS _, Inv_ss pre, Inv_ss post -> t_bdHoareS_conseq pre post tc
  | FeHoareF _ , Inv_ss pre, Inv_ss post -> t_ehoareF_conseq pre post tc
  | FeHoareS _ , Inv_ss pre, Inv_ss post -> t_ehoareS_conseq pre post tc
  | FequivF _  , Inv_ts pre, Inv_ts post -> t_equivF_conseq pre post tc
  | FequivS _  , Inv_ts pre, Inv_ts post -> t_equivS_conseq pre post tc
  | FeagerF _  , Inv_ts pre, Inv_ts post -> t_eagerF_conseq pre post tc
  | _           -> tc_error_noXhl !!tc

(* -------------------------------------------------------------------- *)
let mk_bind_pvar m (id,_) (x, ty) = id, f_pvar x ty m
let mk_bind_glob env m (id,_) x = id, NormMp.norm_glob env m x
let mk_bind_pvars m (bd1,bd2) = List.map2 (mk_bind_pvar m) bd1 bd2
let mk_bind_globs env m (bd1,bd2) = List.map2 (mk_bind_glob env m) bd1 bd2

let cond_equivF_notmod ?(mk_other=false) tc (cond: ts_inv) =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let ef = tc1_as_equivF tc in
  let fl, fr = ef.ef_fl, ef.ef_fr in
  let (mprl,mprr),(mpol,mpor) = Fun.equivF_memenv ef.ef_ml ef.ef_mr fl fr env in
  let fsigl = (Fun.by_xpath fl env).f_sig in
  let fsigr = (Fun.by_xpath fr env).f_sig in
  let pvresl = pv_res and pvresr = pv_res in
  let vresl = LDecl.fresh_id hyps "result_L" in
  let vresr = LDecl.fresh_id hyps "result_R" in
  let fresl = f_local vresl fsigl.fs_ret in
  let fresr = f_local vresr fsigr.fs_ret in
  let ml, mr = fst mpol, fst mpor in
  assert (ml = cond.ml && mr = cond.mr);
  let s = PVM.add env pvresl ml fresl (PVM.add env pvresr mr fresr PVM.empty) in
  let cond = map_ts_inv1 (PVM.subst env s) cond in
  let modil, modir = f_write env fl, f_write env fr in
  let cond, bdgr, bder = generalize_mod_right_ env modir cond in
  let cond, bdgl, bdel = generalize_mod_left_ env modil cond in
  let cond =
    map_ts_inv1 (f_forall_simpl
      [(vresl, GTty fsigl.fs_ret);
       (vresr, GTty fsigr.fs_ret)])
      cond in
  assert (fst mprl = ml && fst mprr = mr);
  let cond = f_forall_mems_ts_inv mprl mprr (map_ts_inv2 f_imp (ef_pr ef) cond) in
  let bmem = [ml;mr] in
  let bother =
    if mk_other then
      mk_bind_pvar ml (vresl,()) (pvresl, fsigl.fs_ret) ::
      mk_bind_pvar mr (vresr,()) (pvresr, fsigr.fs_ret) ::
      List.flatten [mk_bind_globs env ml bdgl; mk_bind_pvars ml bdel;
                    mk_bind_globs env mr bdgr; mk_bind_pvars mr bder]
    else [] in
  cond, bmem, bother

let t_equivF_notmod post tc =
  let ef = tc1_as_equivF tc in
  let post = ts_inv_rebind post ef.ef_ml ef.ef_mr in
  let cond1, _, _ = cond_equivF_notmod tc (map_ts_inv2 f_imp post (ef_po ef)) in
  let cond2 = f_equivF (ef_pr ef) ef.ef_fl ef.ef_fr post in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let cond_equivS_notmod ?(mk_other=false) tc cond =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let sl, sr = es.es_sl, es.es_sr in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  assert (ml = cond.ml && mr = cond.mr);
  let modil, modir = s_write env sl, s_write env sr in
  let cond, bdgr, bder = generalize_mod_right_ env modir cond in
  let cond, bdgl, bdel = generalize_mod_left_ env modil cond in
  let cond = f_forall_mems_ts_inv es.es_ml es.es_mr (map_ts_inv2 f_imp (es_pr es) cond) in
  let bmem = [ml;mr] in
  let bother =
    if mk_other then
      List.flatten [mk_bind_globs env ml bdgl; mk_bind_pvars ml bdel;
                    mk_bind_globs env mr bdgr; mk_bind_pvars mr bder]
    else [] in
  cond, bmem, bother

let t_equivS_notmod post tc =
  let es = tc1_as_equivS tc in
  let post = ts_inv_rebind post (fst es.es_ml) (fst es.es_mr) in
  let cond1,_,_ = cond_equivS_notmod tc (map_ts_inv2 f_imp post (es_po es)) in
  let cond2 = f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) es.es_sl es.es_sr post in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let cond_hoareF_notmod ?(mk_other=false) tc (cond: ss_inv) =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let hf = tc1_as_hoareF tc in
  let f = hf.hf_f in
  let mpr,mpo = Fun.hoareF_memenv hf.hf_m f env in
  let fsig = (Fun.by_xpath f env).f_sig in
  let pvres = pv_res in
  let vres = LDecl.fresh_id hyps "result" in
  let fres = f_local vres fsig.fs_ret in
  let m    = fst mpo in
  let s = PVM.add env pvres m fres PVM.empty in
  let cond = map_ss_inv1 (PVM.subst env s) cond in
  let modi = f_write env f in
  let cond,bdg,bde = generalize_mod_ env modi cond in
  let cond = map_ss_inv1 (f_forall_simpl [(vres, GTty fsig.fs_ret)]) cond in
  let cond = f_forall_mems_ss_inv mpr (map_ss_inv2 f_imp (hf_pr hf) cond) in
  let bmem = [m] in
  let bother =
    if mk_other then
      mk_bind_pvar m (vres,()) (pvres, fsig.fs_ret) ::
      List.flatten [mk_bind_globs env m bdg; mk_bind_pvars m bde]
    else [] in
  cond, bmem, bother

let t_hoareF_notmod (post: ss_inv) tc =
  let hf = tc1_as_hoareF tc in
  let post = ss_inv_rebind post hf.hf_m in
  let cond1, _, _ = cond_hoareF_notmod tc (map_ss_inv2 f_imp post (hf_po hf)) in
  let cond2 = f_hoareF (hf_pr hf) hf.hf_f post in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let cond_hoareS_notmod ?(mk_other=false) tc cond =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_hoareS tc in
  let s = hs.hs_s in
  let m = fst hs.hs_m in
  let modi = s_write env s in
  let cond, bdg, bde = generalize_mod_ env modi cond in
  let cond = f_forall_mems_ss_inv hs.hs_m (map_ss_inv2 f_imp (hs_pr hs) cond) in
  let bmem = [m] in
  let bother =
    if mk_other then
      List.flatten [mk_bind_globs env m bdg; mk_bind_pvars m bde]
    else [] in
  cond, bmem, bother

let t_hoareS_notmod post tc =
  let hs = tc1_as_hoareS tc in
  let post = ss_inv_rebind post (fst hs.hs_m) in
  let cond1, _, _ = cond_hoareS_notmod tc (map_ss_inv2 f_imp post (hs_po hs)) in
  let cond2 = f_hoareS (snd hs.hs_m) (hs_pr hs) hs.hs_s post in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let cond_bdHoareF_notmod ?(mk_other=false) tc (cond: ss_inv) =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let hf = tc1_as_bdhoareF tc in
  let f = hf.bhf_f in
  let mpr,mpo = Fun.hoareF_memenv hf.bhf_m f env in
  let fsig = (Fun.by_xpath f env).f_sig in
  let pvres = pv_res in
  let vres = LDecl.fresh_id hyps "result" in
  let fres = f_local vres fsig.fs_ret in
  let m    = fst mpo in
  let s = PVM.add env pvres m fres PVM.empty in
  let cond = map_ss_inv1 (PVM.subst env s) cond in
  let modi = f_write env f in
  let cond, bdg, bde = generalize_mod_ env modi cond in
  let cond = map_ss_inv1 (f_forall_simpl [(vres, GTty fsig.fs_ret)]) cond in
  assert (fst mpr = m);
  let cond = f_forall_mems_ss_inv mpr (map_ss_inv2 f_imp (bhf_pr hf) cond) in
  let bmem = [m] in
  let bother =
    if mk_other then
      mk_bind_pvar m (vres,()) (pvres, fsig.fs_ret) ::
      List.flatten [mk_bind_globs env m bdg; mk_bind_pvars m bde]
    else [] in
  cond, bmem, bother


let t_bdHoareF_notmod post tc =
  let hf = tc1_as_bdhoareF tc in
  let post = ss_inv_rebind post hf.bhf_m in
  let _, cond =
    bdHoare_conseq_conds hf.bhf_cmp (bhf_pr hf) (bhf_po hf) (bhf_pr hf) post in
  let cond1, _, _ = cond_bdHoareF_notmod tc cond in
  let cond2 = f_bdHoareF (bhf_pr hf) hf.bhf_f post hf.bhf_cmp (bhf_bd hf) in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let cond_bdHoareS_notmod ?(mk_other=false) tc (cond: ss_inv) =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_bdhoareS tc in
  let s = hs.bhs_s in
  let m = fst hs.bhs_m in
  let modi = s_write env s in
  let cond, bdg, bde = generalize_mod_ env modi cond in
  let cond = f_forall_mems_ss_inv hs.bhs_m (map_ss_inv2 f_imp (bhs_pr hs) cond) in
  let bmem = [m] in
  let bother =
    if mk_other then
      List.flatten [mk_bind_globs env m bdg; mk_bind_pvars m bde]
    else [] in
  cond, bmem, bother

let t_bdHoareS_notmod post tc =
  let hs = tc1_as_bdhoareS tc in
  let post = ss_inv_rebind post (fst hs.bhs_m) in
  let _, cond =
    bdHoare_conseq_conds hs.bhs_cmp (bhs_pr hs) (bhs_po hs) (bhs_pr hs) post in
  let cond1, _, _ = cond_bdHoareS_notmod tc cond in
  let cond2 = f_bdHoareS (snd hs.bhs_m) (bhs_pr hs) hs.bhs_s post hs.bhs_cmp (bhs_bd hs) in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let gen_conseq_nm tnm tc pre post =
  FApi.t_internal ~info:"generic-conseq-nm" (fun g ->
    let gs =
      (tnm post @+
        [ t_id;
          tc pre post @+ [t_id; t_trivial; t_id] ]) g in
    FApi.t_swap_goals 0 1 gs
  )

let gen_conseq_nm_ss tnm tc (pre: ss_inv) (post: ss_inv) =
    FApi.t_internal ~info:"generic-conseq-nm" (fun g ->
      let gs =
        (tnm post @+
          [ t_id;
            tc pre post @+ [t_id; t_trivial; t_id] ]) g in
      FApi.t_swap_goals 0 1 gs
    )

let gen_conseq_nm_ts tnm tc (pre: ts_inv) (post: ts_inv) =
  FApi.t_internal ~info:"generic-conseq-nm" (fun g ->
    let gs =
      (tnm post @+
        [ t_id;
          tc pre post @+ [t_id; t_trivial; t_id] ]) g in
    FApi.t_swap_goals 0 1 gs
  )

let t_hoareF_conseq_nm   = gen_conseq_nm_ss t_hoareF_notmod   t_hoareF_conseq
let t_hoareS_conseq_nm   = gen_conseq_nm t_hoareS_notmod   t_hoareS_conseq
let t_equivF_conseq_nm   = gen_conseq_nm_ts t_equivF_notmod   t_equivF_conseq
let t_equivS_conseq_nm   = gen_conseq_nm t_equivS_notmod   t_equivS_conseq
let t_bdHoareF_conseq_nm = gen_conseq_nm t_bdHoareF_notmod t_bdHoareF_conseq
let t_bdHoareS_conseq_nm = gen_conseq_nm t_bdHoareS_notmod t_bdHoareS_conseq

(* -------------------------------------------------------------------- *)
(* concavity (jenhsen) : E(f g2) <= f (E g2)
   {g1} c { g2} : E g2 <= g1
   increasing :f (E g2) <= f g1
   -----------------------------
   {f g1} c { f g2 }
*)

let t_ehoareF_concave (fc: ss_inv) pre post tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_ehoareF tc in
  let f = hf.ehf_f in
  let mpr,mpo = Fun.hoareF_memenv hf.ehf_m f env in
  let fsig = (Fun.by_xpath f env).f_sig in
  let m = fst mpo in
  assert (fst mpr = m && fst mpo = m);
  (* ensure that f only depend of notmod *)
  let modi = f_write env f in
  let modi = PV.add env pv_res fsig.fs_ret modi in
  let fv = PV.fv env m fc.inv in
  let inter = PV.interdep env fv modi in
  if not (PV.is_empty inter) then
    tc_error !!tc "the function should not depend on modified elements: %a"
       (PV.pp env) inter;

  let g0 =
    f_forall_mems_ss_inv (EcMemory.empty_local ~witharg:false m) (map_ss_inv1 f_concave_incr fc) in

  let g1 =
    let cond = map_ss_inv2 (fun pre fc -> f_app_simpl fc [pre] txreal) pre fc in
    let cond = map_ss_inv2 f_xreal_le cond (ehf_pr hf) in
    f_forall_mems_ss_inv mpr cond in

  let g2 =
    let cond = map_ss_inv2 (fun post fc -> f_app_simpl fc [post] txreal) post fc in
    let cond = map_ss_inv2 f_xreal_le (ehf_po hf) cond in
    f_forall_mems_ss_inv mpo cond in

  let g3 =
    f_eHoareF pre f post in

  FApi.xmutate1 tc `HlConseq [g0; g1; g2; g3]

(* -------------------------------------------------------------------- *)
let t_ehoareS_concave (fc: ss_inv) (* xreal -> xreal *) pre post tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_ehoareS tc in
  let s = hs.ehs_s in
  let m = fst hs.ehs_m in
  (* ensure that f only depend of notmod *)
  let modi = s_write env s in
  let fv = PV.fv env m fc.inv in
  let inter = PV.interdep env fv modi in
  if not (PV.is_empty inter) then
    tc_error !!tc "the function should not depend on modified elements: %a"
       (PV.pp env) inter;

  let g0 =
    f_forall_mems_ss_inv hs.ehs_m (map_ss_inv1 f_concave_incr fc) in

  let g1 =
    let cond = map_ss_inv2 (fun pre fc -> f_app_simpl fc [pre] txreal) pre fc in
    let cond = map_ss_inv2 f_xreal_le cond (ehs_pr hs) in
    f_forall_mems_ss_inv hs.ehs_m cond in

  let g2 =
    let cond = map_ss_inv2 (fun post fc -> f_app_simpl fc [post] txreal) post fc in
    let cond = map_ss_inv2 f_xreal_le (ehs_po hs) cond in
    f_forall_mems_ss_inv hs.ehs_m cond in

  let g3 =
    f_eHoareS (snd hs.ehs_m) pre s post in

  FApi.xmutate1 tc `HlConseq [g0; g1; g2; g3]

(* -------------------------------------------------------------------- *)
let t_concave_incr =
  FApi.t_try
    (FApi.t_seq (t_intro_s `Fresh)
       (t_solve ~bases:["concave_incr"] ~mode:EcMatching.fmrigid ~canfail:true ~depth:20))

(* -------------------------------------------------------------------- *)
let t_ehoare_conseq_nm_end =
  [ t_concave_incr;
    t_id;
    t_id;
    t_id ]

(* -------------------------------------------------------------------- *)
let t_ehoareF_conseq_nm pre post tc =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let hf = tc1_as_ehoareF tc in
  let f = hf.ehf_f in
  let _mpr,mpo = Fun.hoareF_memenv hf.ehf_m f env in
  let fsig = (Fun.by_xpath f env).f_sig in
  let _cond1, cond2 = conseq_econd (ehf_pr hf) (ehf_po hf) pre post in

  let pvres = pv_res in
  let vres = LDecl.fresh_id hyps "result" in
  let fres = f_local vres fsig.fs_ret in
  let m    = fst mpo in
  let s = PVM.add env pvres m fres PVM.empty in
  let cond = map_ss_inv1 (PVM.subst env s) cond2 in

  let modi = f_write env f in
  let cond,_,_ = generalize_mod_ env modi cond in
  let cond = map_ss_inv1 (f_forall_simpl [(vres, GTty fsig.fs_ret)]) cond in

  let fc =
    let x = EcIdent.create "x" in
    let f_interp_ehoare_form' cond =
      f_interp_ehoare_form cond (f_local x txreal) in
    map_ss_inv1 (fun cd -> f_lambda [x,GTty txreal] (f_interp_ehoare_form' cd)) cond in

  (t_ehoareF_concave fc pre post @+ t_ehoare_conseq_nm_end) tc

(* -------------------------------------------------------------------- *)
let t_ehoareS_conseq_nm pre post tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_ehoareS tc in
  let s = hs.ehs_s in
  let modi = s_write env s in
  let _cond1, cond2 = conseq_econd (ehs_pr hs) (ehs_po hs) pre post in
  let cond, _bdg, _bde = generalize_mod_ env modi cond2 in
  let fc =
    let x = EcIdent.create "x" in
    let f_interp_ehoare_form' cond =
      f_interp_ehoare_form cond (f_local x txreal) in
    map_ss_inv1 (fun cond -> f_lambda [x,GTty txreal] (f_interp_ehoare_form' cond)) cond in

  (t_ehoareS_concave fc pre post @+ t_ehoare_conseq_nm_end) tc


(* -------------------------------------------------------------------- *)

let process_concave ((info, fc) : pformula option tuple2 gppterm * pformula) tc =
  let hyps, concl = FApi.tc1_flat tc in

  let fc =
    match concl.f_node with
    | FeHoareS hs ->
      let m = fst hs.ehs_m in
      let env = LDecl.push_active_ss hs.ehs_m hyps in
      {m; inv=TTC.pf_process_form !!tc env (tfun txreal txreal) fc}

    | FeHoareF hf ->
      let m = hf.ehf_m in
      let _, env = LDecl.hoareF hf.ehf_m hf.ehf_f hyps in
      {m; inv=TTC.pf_process_form !!tc env (tfun txreal txreal) fc}

    | _ -> tc_error !!tc "conseq concave: not a ehoare judgement"
  in

  let process_cut1 (pre, post) =
    let penv, qenv, gpre, gpost, fmake =
      match concl.f_node with
      | FeHoareS hs ->
        let env = LDecl.push_active_ss hs.ehs_m hyps in
        let fmake pre post = f_eHoareS (snd hs.ehs_m) pre hs.ehs_s post in
        (env, env, (ehs_pr hs), (ehs_po hs), fmake)

      | FeHoareF hf ->
        let penv, qenv = LDecl.hoareF hf.ehf_m hf.ehf_f hyps in
        let fmake pre post =
          f_eHoareF pre hf.ehf_f post in
        (penv, qenv, (ehf_pr hf), (ehf_po hf), fmake)

      | _ -> tc_error !!tc "conseq concave: not a ehoare judgement"
    in

    let pre   = map_ss_inv1 (fun gpre -> pre |> omap (TTC.pf_process_form !!tc penv txreal) |> odfl gpre) gpre  in
    let post  = map_ss_inv1 (fun gpost -> post |> omap (TTC.pf_process_form !!tc qenv txreal) |> odfl gpost) gpost in
    
    fmake pre post

  in

  let f1 = PT.tc1_process_full_closed_pterm_cut
                              ~prcut:(process_cut1) tc info in

  let t_apply_r tc =
    EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true (fst f1) tc in

  match (snd f1).f_node with
  | FeHoareS hs ->
    FApi.t_first t_concave_incr
        (FApi.t_on1seq 3 (t_ehoareS_concave fc (ehs_pr hs) (ehs_po hs)) t_apply_r tc)

  | FeHoareF hf ->
     FApi.t_first t_concave_incr
       (FApi.t_on1seq 3 (t_ehoareF_concave fc (ehf_pr hf) (ehf_po hf)) t_apply_r tc)

  | _ -> tc_error !!tc "conseq concave: not a ehoare judgement"






(* -------------------------------------------------------------------- *)
(*                   Relation between logics                            *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
let t_hoareS_conseq_bdhoare tc =
  let hs = tc1_as_hoareS tc in
  let f_r1 = {m=fst hs.hs_m; inv=f_r1} in
  let concl1 = f_bdHoareS (snd hs.hs_m) (hs_pr hs) hs.hs_s (hs_po hs) FHeq f_r1 in
  FApi.xmutate1 tc `HlConseqBd [concl1]

(* -------------------------------------------------------------------- *)
let t_hoareF_conseq_bdhoare tc =
  let hf = tc1_as_hoareF tc in
  let f_r1 = {m=hf.hf_m; inv=f_r1} in
  let concl1 = f_bdHoareF (hf_pr hf) hf.hf_f (hf_po hf) FHeq f_r1 in
  FApi.xmutate1 tc `HlConseqBd [concl1]

(* -------------------------------------------------------------------- *)
let t_hoareS_conseq_conj pre post pre' post' tc =
  let (_, hyps, _) = FApi.tc1_eflat tc in
  let hs = tc1_as_hoareS tc in
  let pre'' = map_ss_inv2 f_and pre' pre in
  let post'' = map_ss_inv2 f_and post' post in
  if not (ss_inv_alpha_eq hyps (hs_pr hs) pre'') 
    then tc_error !!tc "invalid pre-condition";
  if not (ss_inv_alpha_eq hyps (hs_po hs) post'') 
    then tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareS (snd hs.hs_m) pre hs.hs_s post in
  let concl2 = f_hoareS (snd hs.hs_m) pre' hs.hs_s post' in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)
let t_hoareF_conseq_conj pre post pre' post' tc =
  let (_, hyps, _) = FApi.tc1_eflat tc in
  let hf = tc1_as_hoareF tc in
  let pre'' = map_ss_inv2 f_and pre' pre in
  let post'' = map_ss_inv2 f_and post' post in
  if not (ss_inv_alpha_eq hyps (hf_pr hf) pre'') 
  then tc_error !!tc "invalid pre-condition";
  if not (ss_inv_alpha_eq hyps (hf_po hf) post'')
  then tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareF pre hf.hf_f post in
  let concl2 = f_hoareF pre' hf.hf_f post' in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)
let t_bdHoareS_conseq_conj ~add post post' tc =
  let (_, hyps, _) = FApi.tc1_eflat tc in
  let hs = tc1_as_bdhoareS tc in
  let postc = if add then map_ss_inv2 f_and post' post else post' in
  let posth = if add then post' else map_ss_inv2 f_and post' post in
  if not (ss_inv_alpha_eq hyps (bhs_po hs) postc) then
    tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareS (snd hs.bhs_m) (bhs_pr hs) hs.bhs_s post in
  let concl2 = f_bdHoareS (snd hs.bhs_m) (bhs_pr hs) hs.bhs_s posth 
                 hs.bhs_cmp (bhs_bd hs) in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)
let t_bdHoareF_conseq_conj ~add post post' tc =
  let (_, hyps, _) = FApi.tc1_eflat tc in
  let hs = tc1_as_bdhoareF tc in
  let post = ss_inv_rebind post hs.bhf_m in
  let post' = ss_inv_rebind post' hs.bhf_m in
  let postc = if add then map_ss_inv2 f_and post' post else post' in
  let posth = if add then post' else map_ss_inv2 f_and post' post in
  if not (ss_inv_alpha_eq hyps (bhf_po hs) postc) then
    tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareF (bhf_pr hs) hs.bhf_f post in
  let concl2 = f_bdHoareF (bhf_pr hs) hs.bhf_f posth hs.bhf_cmp (bhf_bd hs) in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)
let t_equivS_conseq_conj pre1 post1 pre2 post2 pre' post' tc =
  let (_, hyps, _) = FApi.tc1_eflat tc in
  let es = tc1_as_equivS tc in
  let (ml, mtl), (mr, mtr) = es.es_ml, es.es_mr in
  let pre1' = ss_inv_generalize_as_left pre1 ml mr in
  let post1' = ss_inv_generalize_as_left post1 ml mr in
  let pre2' = ss_inv_generalize_as_right pre2 ml mr in
  let post2' = ss_inv_generalize_as_right post2 ml mr in
  if not (ts_inv_alpha_eq hyps (es_pr es) (map_ts_inv f_ands [pre';pre1';pre2'])) then
    tc_error !!tc "invalid pre-condition";
  if not (ts_inv_alpha_eq hyps (es_po es) (map_ts_inv f_ands [post';post1';post2'])) then
    tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareS mtl pre1 es.es_sl post1 in
  let concl2 = f_hoareS mtr pre2 es.es_sr post2 in
  let concl3 = f_equivS mtl mtr pre' es.es_sl es.es_sr post' in
  FApi.xmutate1 tc `HlConseqConj [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_equivF_conseq_conj pre1 post1 pre2 post2 pre' post' tc =
  let (_, hyps, _) = FApi.tc1_eflat tc in
  let ef = tc1_as_equivF tc in
  let ml, mr = ef.ef_ml, ef.ef_mr in
  let pre1' = ss_inv_generalize_as_left pre1 ml mr in
  let post1' = ss_inv_generalize_as_left post1 ml mr in
  let pre2' = ss_inv_generalize_as_right pre2 ml mr in
  let post2' = ss_inv_generalize_as_right post2 ml mr in
  let pre'' = ts_inv_rebind pre' ml mr in
  let pre_and = map_ts_inv f_ands [pre''; pre1'; pre2'] in
  let post'' = ts_inv_rebind post' ml mr in
  let post_and = map_ts_inv f_ands [post''; post1'; post2'] in
  if not (ts_inv_alpha_eq hyps (ef_pr ef) pre_and)
  then tc_error !!tc "invalid pre-condition";
  if not (ts_inv_alpha_eq hyps (ef_po ef) post_and)
  then tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareF pre1 ef.ef_fl post1 in
  let concl2 = f_hoareF pre2 ef.ef_fr post2 in
  let concl3 = f_equivF pre' ef.ef_fl ef.ef_fr post' in
  FApi.xmutate1 tc `HlConseqConj [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_equivS_conseq_bd side pr po tc =
  let (_, hyps, _) = FApi.tc1_eflat tc in
  let es = tc1_as_equivS tc in
  let ((ml,_), (mr,_)) = es.es_ml, es.es_mr in
  let m,s,s',prs,pos =
    match side with
    | `Left  ->
      let pos = ss_inv_generalize_as_left po ml mr in
      let prs = ss_inv_generalize_as_left pr ml mr in
      es.es_ml, es.es_sl, es.es_sr, prs, pos
    | `Right -> 
      let pos = ss_inv_generalize_as_right po ml mr in
      let prs = ss_inv_generalize_as_right pr ml mr in
      es.es_mr, es.es_sr, es.es_sl, prs, pos
  in
  if not (List.is_empty s'.s_node) then begin
    let side = side2str (negside side) in
    tc_error !!tc "%s statement should be empty" side
  end;
  if not (ts_inv_alpha_eq hyps prs (es_pr es)) then
    tc_error !!tc "invalid pre- or post-condition";
  if not (ts_inv_alpha_eq hyps pos (es_po es)) then
    tc_error !!tc "invalid pre- or post-condition";
  let f_r1 = {m=fst m; inv=f_r1} in
  let pr = ss_inv_rebind pr (fst m) in
  let po = ss_inv_rebind po (fst m) in
  let g1 = f_bdHoareS (snd m) pr s po FHeq f_r1 in
  FApi.xmutate1 tc `HlBdEquiv [g1]

(* -------------------------------------------------------------------- *)

(*
(forall m1, P1 m1 => exists m2, P m1 m2 /\ P2 m2 /\ q m1 = p m2)
(forall m1 m2, Q m1 m2 => Q2 m2 => Q1 m1)
equiv M1 ~ M2 : P ==> Q   phoare M2 : P2 ==> Q2 R p.
-----------------------------------------------
phoare M1 : P1 ==> Q1 R q.
*)

let transitivity_side_cond ?bds hyps prml poml pomr p q p2 q2 p1 q1 =
  let env = LDecl.toenv hyps in
  let cond1 =
    let fv1 = PV.fv env p.mr p.inv in
    let fv2 = PV.fv env p2.m p2.inv in
    let fv = PV.union fv1 fv2 in
    let fv = match bds with
    | Some (_, bd2) ->
        let fvbd2 = PV.fv env bd2.m bd2.inv in
        PV.union fv fvbd2
    | None -> fv in
    let elts, glob = PV.ntr_elements fv in
    let bd, s = generalize_subst env p2.m elts glob in
    let s1 = PVM.of_mpv s p.mr in
    let s2 = PVM.of_mpv s p2.m in
    let concl = {m=p1.m; inv=f_and (PVM.subst env s1 p.inv) (PVM.subst env s2 p2.inv)} in
    let concl = match bds with
    | Some (bd1, bd2) ->
        let sbd = PVM.of_mpv s bd2.m in
        map_ss_inv2 f_and concl (map_ss_inv1 (fun bd1 -> f_eq bd1 (PVM.subst env sbd bd2.inv)) bd1)
    | None -> concl in
    f_forall_mems_ss_inv prml (map_ss_inv2 f_imp p1 (map_ss_inv1 (f_exists bd) concl)) in
  let cond2 =
    let q1 = ss_inv_generalize_as_left q1 q.ml q.mr in
    let q2 = ss_inv_generalize_as_right q2 q.ml q.mr in
    f_forall_mems_ts_inv poml pomr (map_ts_inv3 (fun q q2 q1 -> f_imps [q;q2] q1) q q2 q1) in
  (cond1, cond2)

let t_hoareF_conseq_equiv f2 p q p2 q2 tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let hf1 = tc1_as_hoareF tc in
  let ef  = f_equivF p hf1.hf_f f2 q in
  let hf2 = f_hoareF p2 f2 q2 in
  let (prml, _prmr), (poml, pomr) = Fun.equivF_memenv p.ml p.mr hf1.hf_f f2 env in
  let (cond1, cond2) =
    transitivity_side_cond hyps prml poml pomr p q p2 q2 (hf_pr hf1) (hf_po hf1) in
  FApi.xmutate1 tc `HoareFConseqEquiv [cond1; cond2; ef; hf2]

let t_bdHoareF_conseq_equiv f2 p q p2 q2 bd2 tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let hf1 = tc1_as_bdhoareF tc in
  let ef  = f_equivF p hf1.bhf_f f2 q in
  let hf2 = f_bdHoareF p2 f2 q2 hf1.bhf_cmp bd2 in
  let (prml, _prmr), (poml, pomr) = Fun.equivF_memenv p.ml p.mr hf1.bhf_f f2 env in
  let (cond1, cond2) =
    transitivity_side_cond ~bds:(bhf_bd hf1, bd2) hyps prml poml pomr p q p2 q2 (bhf_pr hf1) (bhf_po hf1) in
  FApi.xmutate1 tc `BdHoareFConseqEquiv [cond1; cond2; ef; hf2]


let t_ehoareF_conseq_equiv f2 p q p2 q2 tc =
  let env = FApi.tc1_env tc in
  let hf1 = tc1_as_ehoareF tc in
  let ef  = f_equivF p hf1.ehf_f f2 q in
  let hf2 = f_eHoareF p2 f2 q2 in
  let (prml, _prmr), (poml, pomr) = Fun.equivF_memenv p.ml p.mr hf1.ehf_f f2 env in
  let p1 = (ehf_pr hf1) and q1 = (ehf_po hf1) in
  let cond1 =
    let fv1 = PV.fv env p.mr p.inv in
    let fv2 = PV.fv env p2.m p2.inv in
    let fv = PV.union fv1 fv2 in
    let elts, glob = PV.ntr_elements fv in
    let bd, s = generalize_subst env p2.m elts glob in
    let s1 = PVM.of_mpv s p.mr in
    let s2 = PVM.of_mpv s p2.m in
    let p1 = ss_inv_rebind p1 p.ml in
    let concl =
     f_or (f_eq p1.inv f_xreal_inf)
       (f_and (PVM.subst env s1 p.inv) (f_xreal_le (PVM.subst env s2 p2.inv) p1.inv)) in
    f_forall_mems [prml] (f_exists bd concl) in
  let cond2 =
    let q1 = ss_inv_rebind q1 q.ml in
    let q1 = ss_inv_generalize_right q1 q.mr in
    let q2 = ss_inv_rebind q2 q.mr in
    let q2 = ss_inv_generalize_left q2 q.ml in
    f_forall_mems_ts_inv poml pomr (map_ts_inv3 (fun q q1 q2 -> f_imp q (f_xreal_le q1 q2)) q q1 q2) in
  FApi.xmutate1 tc `HoareFConseqEquiv [cond1; cond2; ef; hf2]


(* -------------------------------------------------------------------- *)
let rec t_hi_conseq notmod f1 f2 f3 tc =
  let t_mytrivial = fun tc -> t_simplify ?target:None ~delta:`No tc in
  let t_mytrivial = [t_mytrivial; t_split; t_fail] in
  let t_mytrivial = FApi.t_try (FApi.t_seqs t_mytrivial) in
  let t_on1       = FApi.t_on1 ~ttout:t_mytrivial in
  let t_on1seq    = FApi.t_on1seq ~ttout:t_mytrivial in

  let check_is_detbound who bound =
    if not (EcFol.f_equal bound f_r1) then
      tc_error_lazy !!tc (fun fmt ->
        let who =
          match who with
          | `First  -> "first"
          | `Second -> "second"
          | `Third  -> "third"
        in
          Format.fprintf fmt
            "the bound of the %s parameter should be exactly 1%%r"
            who)
  in

  let t_apply_r (pt, _f) tc =
    match pt with
    | Some pt -> EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt tc

    | None    -> EcPhlTAuto.t_hoare_true tc
  in

  let concl = FApi.tc1_goal tc in

  match concl.f_node, f1, f2, f3 with
  (* ------------------------------------------------------------------ *)
  (* hoareS / hoareS / ⊥ / ⊥                                            *)
  | FhoareS _, Some ((_, {f_node = FhoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_hoareS_conseq_nm else t_hoareS_conseq in
    t_on1 2 (t_apply_r nf1) (tac (hs_pr hs) (hs_po hs) tc)

  (* ------------------------------------------------------------------ *)
  (* hoareS / hoareS / hoareS / ⊥                                       *)
  | FhoareS _,
      Some ((_, { f_node = FhoareS hs }) as nf1),
      Some ((_, f2) as nf2),
      None
    ->
    let hs2 = pf_as_hoareS !!tc f2 in
    let tac = if notmod then t_hoareS_conseq_nm else t_hoareS_conseq in

    t_on1seq 2
      (tac (map_ss_inv2 f_and (hs_pr hs) (hs_pr hs2)) 
            (map_ss_inv2 f_and (hs_po hs) (hs_po hs2)))
      (FApi.t_seqsub
         (t_hoareS_conseq_conj (hs_pr hs2) (hs_po hs2) (hs_pr hs) (hs_po hs))
         [t_apply_r nf2; t_apply_r nf1])
      tc

  (* ------------------------------------------------------------------ *)
  (* hoareS / bdhoareS / ⊥ / ⊥                                          *)
  | FhoareS _, Some ((_, {f_node = FbdHoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in

    check_is_detbound `First (bhs_bd hs).inv;

    FApi.t_seq
      t_hoareS_conseq_bdhoare
      (t_on1seq 1
         (t_bdHoareS_conseq_bd hs.bhs_cmp (bhs_bd hs))
         (t_on1seq 2 (tac (bhs_pr hs) (bhs_po hs)) (t_apply_r nf1)))
      tc

  (* ------------------------------------------------------------------ *)
  (* hoareF / hoareF / ⊥ / ⊥                                            *)
  | FhoareF _, Some ((_, {f_node = FhoareF hs}) as nf1), None, None ->
    let tac = if notmod then t_hoareF_conseq_nm else t_hoareF_conseq in
    t_on1 2 (t_apply_r nf1) (tac (hf_pr hs) (hf_po hs) tc)

  (* ------------------------------------------------------------------ *)
  (* hoareF / hoareF / hoareF / ⊥                                       *)
  | FhoareF _,
      Some ((_, {f_node = FhoareF hf}) as nf1),
      Some((_, f2) as nf2),
      None
    ->
    let hs2 = pf_as_hoareF !!tc f2 in
    let tac = if notmod then t_hoareF_conseq_nm else t_hoareF_conseq in
    let pr1, po1 = hf_pr hf, hf_po hf in
    let pr2 = ss_inv_rebind (hf_pr hs2) hf.hf_m in
    let po2 = ss_inv_rebind (hf_po hs2) hf.hf_m in
    (* check that the pre- and post-conditions are well formed *)
    t_on1seq 2
      ((tac (map_ss_inv2 f_and pr1 pr2) 
           (map_ss_inv2 f_and po1 po2)))
      (FApi.t_seqsub
         (t_hoareF_conseq_conj pr2 po2 pr1 po1)
         [t_apply_r nf2; t_apply_r nf1])
      tc

  (* ------------------------------------------------------------------ *)
  (* hoareF / bdhoareF / ⊥ / ⊥                                            *)
  | FhoareF _, Some ((_, {f_node = FbdHoareF hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareF_conseq_nm else t_bdHoareF_conseq in

    check_is_detbound `First (bhf_bd hs).inv;

    FApi.t_seq
      t_hoareF_conseq_bdhoare
      (t_on1seq 1
         (t_bdHoareF_conseq_bd hs.bhf_cmp (bhf_bd hs))
         (t_on1seq 2 (tac (bhf_pr hs) (bhf_po hs)) (t_apply_r nf1)))
      tc
  (* ------------------------------------------------------------------ *)
  (* hoareF / equivF / hoareF                                           *)
  | FhoareF _,
    Some ((_, {f_node = FequivF ef}) as nef), Some((_, f2) as nf2), _ ->
    let hf2 = pf_as_hoareF !!tc f2 in
    FApi.t_seqsub
      (t_hoareF_conseq_equiv hf2.hf_f (ef_pr ef) (ef_po ef) (hf_pr hf2) (hf_po hf2))
      [t_id; t_id; t_apply_r nef; t_apply_r nf2] tc

  (* ------------------------------------------------------------------ *)
  (* ehoareS / ehoareS / ⊥ / ⊥                                            *)
  | FeHoareS _, Some ((_, {f_node = FeHoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_ehoareS_conseq_nm else t_ehoareS_conseq in
    FApi.t_last (t_apply_r nf1) (tac (ehs_pr hs) (ehs_po hs) tc)

  (* ------------------------------------------------------------------ *)
  (* ehoareF / ehoareF / ⊥ / ⊥                                            *)
  | FeHoareF _, Some ((_, {f_node = FeHoareF hf}) as nf1), None, None ->
    let tac = if notmod then t_ehoareF_conseq_nm else t_ehoareF_conseq in
    FApi.t_last (t_apply_r nf1) (tac (ehf_pr hf) (ehf_po hf) tc)

  (* ------------------------------------------------------------------ *)
  (* ehoareF / equivF / ehoareF                                           *)
  | FeHoareF _,
    Some ((_, {f_node = FequivF ef}) as nef), Some((_, f2) as nf2), _ ->
    let hf2 = pf_as_ehoareF !!tc f2 in
    FApi.t_seqsub
      (t_ehoareF_conseq_equiv hf2.ehf_f (ef_pr ef) (ef_po ef) (ehf_pr hf2) (ehf_po hf2))
      [t_id; t_id; t_apply_r nef; t_apply_r nf2] tc

  (* ------------------------------------------------------------------ *)
  (* bdhoareS / bdhoareS / ⊥ / ⊥                                        *)
  | FbdHoareS _, Some ((_, {f_node = FbdHoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in

    t_on1seq 1
      (t_bdHoareS_conseq_bd hs.bhs_cmp (bhs_bd hs))
      (t_on1seq 2 (tac (bhs_pr hs) (bhs_po hs)) (t_apply_r nf1))
      tc

  (* ------------------------------------------------------------------ *)
  (* bdhoareS / bdhoareS / hoareS / ⊥                                   *)
  | FbdHoareS hs0,
      Some ((_, {f_node = FbdHoareS hs}) as nf1),
      Some ((_, f2) as nf2),
      None
    ->
    let hs2 = pf_as_hoareS !!tc f2 in
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in

    let m,hi,hh, h0 =
      as_seq4 (LDecl.fresh_ids (FApi.tc1_hyps tc) ["&m";"_";"_";"_"]) in
    let pre    = map_ss_inv2 f_and (bhs_pr hs) (hs_pr hs2) in
    let mpre   = Fsubst.f_subst_mem pre.m m pre.inv in
    let post1  = (bhs_po hs0) in
    let post   = (bhs_po hs) in
    let posta  = map_ss_inv2 f_and post (hs_po hs2) in

    let concl1 = f_forall_mems_ss_inv hs0.bhs_m (map_ss_inv2 f_imp (bhs_pr hs0) pre) in

    let tc = ( t_cut concl1 @+
        [ t_id;   (* subgoal 1 : pre *)
          t_intro_i hi @!
          t_cut (f_hoareS (snd hs2.hs_m) pre hs2.hs_s (hs_po hs2)) @+ [
            t_hoareS_conseq (hs_pr hs2) (hs_po hs2) @+
                [ EcLowGoal.t_trivial;
                  t_mytrivial;
                  t_clear hi (* subgoal 2 : hs2 *)];
            t_intro_i hh @!
            (t_bdHoareS_conseq_bd hs.bhs_cmp (bhs_bd hs) @+ [
              t_id; (* subgoal 3 : bound *)
              t_bdHoareS_conseq_conj ~add:false (hs_po hs2) post1 @+ [
                t_hoareS_conseq pre (hs_po hs2) @+ [
                  t_intros_i [m;h0] @! t_cutdef
                    (ptlocal ~args:[pamemory m; palocal h0] hi)
                    mpre @! EcLowGoal.t_trivial;
                  t_mytrivial;
                  t_apply_hyp hh];
                tac pre posta @+ [
                  t_apply_hyp hi;
                  t_id; (* subgoal 4 : post *)
                  t_bdHoareS_conseq_conj ~add:true (hs_po hs2) post @+ [
                    t_apply_hyp hh;
                    t_bdHoareS_conseq (bhs_pr hs) post @+ [
                      EcLowGoal.t_trivial;
                      t_mytrivial;
                      t_id (* subgoal 5 : bdhoare *)
                    ]
                  ]
                ]
              ]
            ]) @! t_clears [hh; hi]
          ]
        ]) tc in

    let tc = FApi.t_swap_goals 1 1 (FApi.t_swap_goals 1 2 tc) in

    FApi.t_sub
      [t_mytrivial; t_mytrivial; t_mytrivial; t_apply_r nf2; t_apply_r nf1]
      tc

  (* ------------------------------------------------------------------ *)
  (* bdhoareF / bdhoareF / ⊥ / ⊥                                        *)
  | FbdHoareF _, Some ((_, {f_node = FbdHoareF hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareF_conseq_nm else t_bdHoareF_conseq in

    t_on1seq 1
      (t_bdHoareF_conseq_bd hs.bhf_cmp (bhf_bd hs))
      (t_on1seq 2 (tac (bhf_pr hs) (bhf_po hs)) (t_apply_r nf1))
      tc

  (* ------------------------------------------------------------------ *)
  (* bdhoareF / bdhoareF / hoareF / ⊥                                  *)
  | FbdHoareF hs0,
      Some ((_, {f_node = FbdHoareF hs}) as nf1),
      Some ((_, f2) as nf2),
      None
    ->

    let hs2 = pf_as_hoareF !!tc f2 in
    let tac = if notmod then t_bdHoareF_conseq_nm else t_bdHoareF_conseq in
    let m,hi,hh, h0 =
      as_seq4 (LDecl.fresh_ids (FApi.tc1_hyps tc) ["&m";"_";"_";"_"]) in
    let hs_pr = ss_inv_rebind (bhf_pr hs) hs2.hf_m in
    let hs0_pr = ss_inv_rebind (bhf_pr hs0) hs2.hf_m in
    let pre    = map_ss_inv2 f_and hs_pr (hf_pr hs2) in
    let mpre   = Fsubst.f_subst_mem pre.m m pre.inv in
    let post1  = (bhf_po hs0) in
    let post   = ss_inv_rebind (bhf_po hs) hs2.hf_m in
    let posta  = map_ss_inv2 f_and post (hf_po hs2) in
    let mpr,_ = EcEnv.Fun.hoareF_memenv hs0.bhf_m hs0.bhf_f (FApi.tc1_env tc) in
    let concl1 = f_forall_mems_ss_inv mpr (map_ss_inv2 f_imp hs0_pr pre) in

    let tc = ( t_cut concl1 @+
        [ t_id;   (* subgoal 1 : pre *)
          t_intro_i hi @!
          t_cut (f_hoareF pre hs2.hf_f (hf_po hs2)) @+ [
            t_hoareF_conseq (hf_pr hs2) (hf_po hs2) @+
                [ EcLowGoal.t_trivial;
                  t_mytrivial;
                  t_clear hi (* subgoal 2 : hs2 *)];
            t_intro_i hh @!
            (t_bdHoareF_conseq_bd hs.bhf_cmp (bhf_bd hs) @+ [
              t_id; (* subgoal 3 : bound *)
              t_bdHoareF_conseq_conj ~add:false (hf_po hs2) post1 @+ [
                t_hoareF_conseq pre (hf_po hs2) @+ [
                  t_intros_i [m;h0] @! t_cutdef
                    (ptlocal ~args:[pamemory m; palocal h0] hi)
                    mpre @! EcLowGoal.t_trivial;
                  t_mytrivial @! t_intros_i [m; h0] @! t_apply_hyp h0;
                  t_apply_hyp hh];
                tac pre posta @+ [
                  t_apply_hyp hi;
                  t_id; (* subgoal 4 : post *)
                  t_bdHoareF_conseq_conj ~add:true (hf_po hs2) post @+ [
                    t_apply_hyp hh;
                    t_bdHoareF_conseq (bhf_pr hs) post @+ [
                      EcLowGoal.t_trivial;
                      t_mytrivial;
                      t_id (* subgoal 5 : bdhoare *)
                    ]
                  ]
                ]
              ]
            ]) @! t_clears [hh; hi]
          ]
        ]) tc in

    let tc = FApi.t_swap_goals 1 1 (FApi.t_swap_goals 1 2 tc) in

    FApi.t_sub
      [t_mytrivial; t_mytrivial; t_mytrivial; t_apply_r nf2; t_apply_r nf1]
      tc

  (* ------------------------------------------------------------------ *)
  (* bdhoareF / equivF / bdhoareF                                       *)
  | FbdHoareF _,
    Some ((_, {f_node = FequivF ef}) as nef), Some((_, f2) as nf2), _ ->
    let hf2 = pf_as_bdhoareF !!tc f2 in
    FApi.t_seqsub
      (t_bdHoareF_conseq_equiv hf2.bhf_f (ef_pr ef) (ef_po ef) 
                                         (bhf_pr hf2) (bhf_po hf2) (bhf_bd hf2))
      [t_id; t_id; t_apply_r nef; t_apply_r nf2] tc

  (* ------------------------------------------------------------------ *)
  (* equivS / equivS / ⊥ / ⊥                                            *)
  | FequivS _, Some ((_, {f_node = FequivS es}) as nf1), None, None ->
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in
    t_on1 2 (t_apply_r nf1) (tac (es_pr es) (es_po es) tc)

  (* ------------------------------------------------------------------ *)
  (* equivS / equivS / hoareS / hoareS  *)
  | FequivS _,
      Some ((_, {f_node = FequivS es}) as nf1),
      Some ((_, f2) as nf2),
      Some ((_, f3) as nf3)
    ->
    let hs2    = pf_as_hoareS !!tc f2 in
    let hs3    = pf_as_hoareS !!tc f3 in
    let (ml, mr) = (fst es.es_ml, fst es.es_mr) in
    let hs2_pr = ss_inv_generalize_as_left (hs_pr hs2) ml mr in
    let hs2_po = ss_inv_generalize_as_left (hs_po hs2) ml mr in
    let hs3_pr = ss_inv_generalize_as_right (hs_pr hs3) ml mr in
    let hs3_po = ss_inv_generalize_as_right (hs_po hs3) ml mr in
    let pre    = map_ts_inv f_ands [es_pr es; hs2_pr; hs3_pr] in
    let post   = map_ts_inv f_ands [es_po es; hs2_po; hs3_po] in
    let tac    = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    t_on1seq 2 (tac pre post)
      (FApi.t_seqsub
         (t_equivS_conseq_conj
            (hs_pr hs2) (hs_po hs2) (hs_pr hs3) (hs_po hs3) (es_pr es) (es_po es))
         [t_apply_r nf2; t_apply_r nf3; t_apply_r nf1])
      tc

  (* ------------------------------------------------------------------ *)
  (* equivS / equivS / bdhoareS / ⊥                                     *)
  | FequivS _, Some (_, {f_node = FequivS es}), Some (_, f), None
      when is_bdHoareS f
    ->
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    t_on1seq 2
      (tac (es_pr es) (es_po es))
      (t_hi_conseq notmod None f2 None)
      tc

  (* ------------------------------------------------------------------ *)
  (* equivS / equivS / ⊥ / bdhoareS                                     *)
  | FequivS _, Some (_, {f_node = FequivS es}), None, Some (_, f)
      when is_bdHoareS f
    ->
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    t_on1seq 2
      (tac (es_pr es) (es_po es))
      (t_hi_conseq notmod None None f3)
      tc

  (* ------------------------------------------------------------------ *)
  (* equivS / ? / ? / ⊥                                                 *)
  | FequivS es, Some _, Some _, None ->
    let m = EcIdent.create "&hr" in
    let f3 = f_hoareS (snd es.es_mr) {m;inv=f_true} es.es_sr {m;inv=f_true} in
    t_hi_conseq notmod f1 f2 (Some (None, f3)) tc

  (* ------------------------------------------------------------------ *)
  (* equivS / ? / ⊥ / ?                                                 *)
  | FequivS es, Some _, None, Some _ ->
    let m = EcIdent.create "&hr" in
    let f2 = f_hoareS (snd es.es_ml) {m;inv=f_true} es.es_sl {m;inv=f_true} in
    t_hi_conseq notmod f1 (Some (None, f2)) f3 tc

  (* ------------------------------------------------------------------ *)
  (* equivS / ⊥ / bdhoareS / ⊥                                          *)
  | FequivS es, None, Some ((_, f2) as nf2), None ->
    let hs = pf_as_bdhoareS !!tc f2 in
    let (ml, mr) = (fst es.es_ml, fst es.es_mr) in
    let pre = ss_inv_generalize_as_left (bhs_pr hs) ml mr in
    let post = ss_inv_generalize_as_left (bhs_po hs) ml mr in
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    check_is_detbound `Second (bhs_bd hs).inv;

    t_on1seq 2
     (tac pre post)
     (FApi.t_seq
        (t_equivS_conseq_bd `Left (bhs_pr hs) (bhs_po hs))
        (t_apply_r nf2))
     tc

  (* ------------------------------------------------------------------ *)
  (* equivS / ⊥ / ⊥ / bdhoareS                                          *)
  | FequivS es, None, None, Some ((_, f3) as nf3) ->
    let hs = pf_as_bdhoareS !!tc f3 in
    let (ml, mr) = (fst es.es_ml, fst es.es_mr) in
    let pre = ss_inv_generalize_as_right (bhs_pr hs) ml mr in
    let post = ss_inv_generalize_as_right (bhs_po hs) ml mr in
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    check_is_detbound `Third (bhs_bd hs).inv;

    t_on1seq 2
      (tac pre post)
      (FApi.t_seq
         (t_equivS_conseq_bd `Right (bhs_pr hs) (bhs_po hs))
         (t_apply_r nf3))
      tc

  (* ------------------------------------------------------------------ *)
  (* equivF / equivF / ⊥ / ⊥                                            *)
  | FequivF _, Some ((_, {f_node = FequivF ef}) as nf1), None, None ->
    let tac = if notmod then t_equivF_conseq_nm else t_equivF_conseq in
    t_on1seq 2 (tac (ef_pr ef) (ef_po ef)) (t_apply_r nf1) tc

  (* ------------------------------------------------------------------ *)
  (* equivF / equivF / hoareF / hoareF                                  *)
  | FequivF _,
      Some ((_, {f_node = FequivF ef}) as nf1),
      Some ((_, f2) as nf2),
      Some ((_, f3) as nf3)
    ->
    let hs2    = pf_as_hoareF !!tc f2 in
    let hs3    = pf_as_hoareF !!tc f3 in
    let (ml, mr) = (ef.ef_ml, ef.ef_mr) in
    let hs2_pr = ss_inv_generalize_as_left (hf_pr hs2) ml mr in
    let hs3_pr = ss_inv_generalize_as_right (hf_pr hs3) ml mr in
    let pre    = map_ts_inv f_ands [ef_pr ef; hs2_pr; hs3_pr] in
    let hs2_po = ss_inv_generalize_as_left (hf_po hs2) ml mr in
    let hs3_po = ss_inv_generalize_as_right (hf_po hs3) ml mr in
    let post  = map_ts_inv f_ands [ef_po ef; hs2_po; hs3_po] in
    let tac    = if notmod then t_equivF_conseq_nm else t_equivF_conseq in
    t_on1seq 2
      (tac pre post)
      (FApi.t_seqsub
         (t_equivF_conseq_conj
            (hf_pr hs2) (hf_po hs2) (hf_pr hs3) (hf_po hs3) (ef_pr ef) (ef_po ef))
         [t_apply_r nf2; t_apply_r nf3; t_apply_r nf1])
      tc

  (* ------------------------------------------------------------------ *)
  (* equivF / ? / ? / ⊥                                                 *)
  | FequivF ef, Some _, Some _, None ->
    let m = EcIdent.create "&hr" in
    let f3 = f_hoareF {m;inv=f_true} ef.ef_fr {m;inv=f_true} in
    t_hi_conseq notmod f1 f2 (Some (None, f3)) tc

  (* ------------------------------------------------------------------ *)
  (* equivF / ? / ⊥ / ?                                                 *)
  | FequivF ef, Some _, None, Some _ ->
    let m = EcIdent.create "&hr" in
    let f2 = f_hoareF {m;inv=f_true} ef.ef_fl {m;inv=f_true} in
    t_hi_conseq notmod f1 (Some (None, f2)) f3 tc

  | _ ->
    let rec pp_f f =
      match f.f_node with
      | FequivF   _ -> "equivF"
      | FequivS   _ -> "equivS"
      | FhoareF   _ -> "hoareF"
      | FhoareS   _ -> "hoareS"
      | FbdHoareF _ -> "phoareF"
      | FbdHoareS _ -> "phoareS"
      | _           -> "?"

    and pp_o f =
      match f with
      | None -> "_"
      | Some (_, f) -> pp_f f
    in

    tc_error_lazy !!tc (fun fmt ->
      Format.fprintf fmt
        "do not how to combine %s and %s and %s into %s"
        (pp_o f1) (pp_o f2) (pp_o f3) (pp_f concl))

(* -------------------------------------------------------------------- *)
type processed_conseq_info =
  | PCI_bd of hoarecmp option * ss_inv

let process_info pe hyps m = function
  | CQI_bd (cmp, bd) -> PCI_bd (cmp, {m; inv=TTC.pf_process_form pe hyps treal bd})

let process_conseq notmod ((info1, info2, info3) : conseq_ppterm option tuple3) tc =
  let hyps, concl = FApi.tc1_flat tc in

  let ensure_none o =
    if not (is_none o) then tc_error !!tc "cannot give a bound here" in

  let process_cut1 ((pre, post), bd) =
     let penv, qenv, gpre, gpost, ty, fmake =
      match concl.f_node with
      | FhoareS hs ->
        let env = LDecl.push_active_ss hs.hs_m hyps in

        let fmake pre post c_or_bd =
          match c_or_bd with
          | None ->
            f_hoareS(snd hs.hs_m) pre hs.hs_s post
          | Some (PCI_bd (cmp, bd)) ->
            f_bdHoareS (snd hs.hs_m) pre hs.hs_s post (oget cmp) bd
        in (env, env, Inv_ss (hs_pr hs), Inv_ss (hs_po hs), tbool, lift_ss_inv2 fmake)

      | FhoareF hf ->
        let penv, qenv = LDecl.hoareF hf.hf_m hf.hf_f hyps in

        let fmake pre post c_or_bd =
          match c_or_bd with
          | None ->
            f_hoareF pre hf.hf_f post
          | Some (PCI_bd (cmp, bd)) ->
            f_bdHoareF pre hf.hf_f post (oget cmp) bd

        in (penv, qenv, Inv_ss (hf_pr hf), Inv_ss (hf_po hf), tbool, lift_ss_inv2 fmake)

      | FeHoareS hs ->
        let env = LDecl.push_active_ss hs.ehs_m hyps in
        let fmake pre post bd =
          ensure_none bd;
          f_eHoareS (snd hs.ehs_m) pre hs.ehs_s post in
        (env, env, Inv_ss (ehs_pr hs), Inv_ss (ehs_po hs), txreal, lift_ss_inv2 fmake)

      | FeHoareF hf ->
        let penv, qenv = LDecl.hoareF hf.ehf_m hf.ehf_f hyps in
        let fmake pre post bd =
          ensure_none bd;
          f_eHoareF pre hf.ehf_f post in
        (penv, qenv, Inv_ss (ehf_pr hf), Inv_ss (ehf_po hf), txreal, lift_ss_inv2 fmake)

      | FbdHoareS bhs ->
        let env = LDecl.push_active_ss bhs.bhs_m hyps in

        let fmake pre post c_or_bd =
          match c_or_bd with
          | None                   ->
            f_bdHoareS (snd bhs.bhs_m) pre bhs.bhs_s post bhs.bhs_cmp (bhs_bd bhs)
          | Some (PCI_bd (cmp,bd)) ->
            let cmp = odfl bhs.bhs_cmp cmp in
            f_bdHoareS (snd bhs.bhs_m) pre bhs.bhs_s post cmp bd in

        (env, env, Inv_ss (bhs_pr bhs), Inv_ss (bhs_po bhs), tbool, lift_ss_inv2 fmake)

      | FbdHoareF hf ->
        let penv, qenv = LDecl.hoareF hf.bhf_m hf.bhf_f hyps in

        let fmake pre post c_or_bd =
          match c_or_bd with
          | None                   ->
            f_bdHoareF pre hf.bhf_f post hf.bhf_cmp (bhf_bd hf)
          | Some (PCI_bd (cmp,bd)) ->
            let cmp = odfl hf.bhf_cmp cmp in
            f_bdHoareF pre hf.bhf_f post cmp bd
        in

        (penv, qenv, Inv_ss (bhf_pr hf), Inv_ss (bhf_po hf), tbool, lift_ss_inv2 fmake)

      | FequivF ef ->
        let penv, qenv = LDecl.equivF ef.ef_ml ef.ef_mr ef.ef_fl ef.ef_fr hyps in
        let fmake pre post c_or_bd =
          ensure_none c_or_bd;
          f_equivF pre ef.ef_fl ef.ef_fr post
        in (penv, qenv, Inv_ts (ef_pr ef), Inv_ts (ef_po ef), tbool, lift_ts_inv2 fmake)

      | FequivS es ->
        let env = LDecl.push_active_ts es.es_ml es.es_mr hyps in
        let fmake pre post c_or_bd =
          ensure_none c_or_bd;
          f_equivS (snd es.es_ml) (snd es.es_mr) pre es.es_sl es.es_sr post
        in (env, env, Inv_ts (es_pr es), Inv_ts (es_po es), tbool, lift_ts_inv2 fmake)

      | _ -> tc_error !!tc "conseq: not a phl/prhl judgement"
    in

    let pre  = pre  |> omap (TTC.pf_process_form !!tc penv ty) |> odfl (inv_of_inv gpre)  in
    let post = post |> omap (TTC.pf_process_form !!tc qenv ty) |> odfl (inv_of_inv gpost) in

    let (pre, post, bd) = match gpre, gpost with
    | Inv_ss gpre, Inv_ss gpost ->
        let bd = bd |> omap (process_info !!tc penv gpre.m) in
        (Inv_ss {inv=pre;m=gpre.m}, Inv_ss {inv=post;m=gpost.m}, bd)
    | Inv_ts gpre, Inv_ts gpost ->
        ensure_none bd;
        (Inv_ts {inv=pre;ml=gpre.ml;mr=gpost.mr},
         Inv_ts {inv=post;ml=gpost.ml;mr=gpost.mr},
         None)
    | _ -> tc_error !!tc "conseq: pre and post must be of the same kind" in

    fmake pre post bd
  in

  let process_cut2 side f1 ((pre, post), c_or_bd) =
    let penv, qenv, gpre, gpost, ty, fmake =
      match concl.f_node with
      | FhoareS hs ->
        let env = LDecl.push_active_ss hs.hs_m hyps in
        let fmake pre post c_or_bd =
          ensure_none c_or_bd;
          f_hoareS (snd hs.hs_m) pre hs.hs_s post
        in (env, env, Inv_ss (hs_pr hs), Inv_ss (hs_po hs), tbool, lift_ss_inv2 fmake)

      | FhoareF hf ->
        let m = hf.hf_m in
        let f, pr, po = match f1 with
        | None -> hf.hf_f, hf_pr hf, hf_po hf
        | Some f1 -> match (snd f1).f_node with
                     | FequivF ef when side = `Left -> 
                      ef.ef_fr, {m; inv=f_true}, {m; inv=f_true}
                     | _ -> hf.hf_f, hf_pr hf, hf_po hf
        in
        let penv, qenv = LDecl.hoareF m f hyps in
        let fmake pre post c_or_bd =
          ensure_none c_or_bd; f_hoareF pre f post in
        (penv, qenv, Inv_ss pr, Inv_ss po, tbool, lift_ss_inv2 fmake)

      | FeHoareF hf ->
        let f, pr, po, m = match f1 with
        | None -> hf.ehf_f, ehf_pr hf, ehf_po hf, hf.ehf_m
        | Some f1 -> match (snd f1).f_node with
                     | FequivF ef when side = `Left ->
                         let f_xreal_1 = f_r2xr f_r1 in
                         ef.ef_fr, {m=ef.ef_mr; inv=f_xreal_1}, 
                          {m=ef.ef_mr; inv=f_xreal_1}, ef.ef_mr
                     | _ -> hf.ehf_f, ehf_pr hf, ehf_po hf, hf.ehf_m
        in
        let penv, qenv = LDecl.hoareF m f hyps in
        let fmake pre post c_or_bd =
          ensure_none c_or_bd; f_eHoareF pre f post in
        (penv, qenv, Inv_ss pr, Inv_ss po, txreal, lift_ss_inv2 fmake)

      | FbdHoareS bhs ->
        let env = LDecl.push_active_ss bhs.bhs_m hyps in
        let fmake pre post c_or_bd =
          ensure_none c_or_bd;
          f_hoareS (snd bhs.bhs_m) pre bhs.bhs_s post
        in (env, env, Inv_ss (bhs_pr bhs), Inv_ss (bhs_po bhs), tbool, lift_ss_inv2 fmake)

      | FbdHoareF bhf ->
        let f, pr, po, m = match f1 with
        | None -> bhf.bhf_f, bhf_pr bhf, bhf_po bhf, bhf.bhf_m
        | Some f1 -> match (snd f1).f_node with
                     | FequivF ef when side = `Left -> ef.ef_fr, 
                        {m=ef.ef_mr;inv=f_true}, {m=ef.ef_mr;inv=f_true}, ef.ef_mr
                     | _ -> bhf.bhf_f, bhf_pr bhf, bhf_po bhf, bhf.bhf_m
        in
        let penv, qenv = LDecl.hoareF m f hyps in
        let fmake pre post c_or_bd =
          ensure_none c_or_bd; f_hoareF pre f post in
        (penv, qenv, Inv_ss pr, Inv_ss po, tbool, lift_ss_inv2 fmake)

      | FequivF ef ->
        let f = sideif side ef.ef_fl ef.ef_fr in
        let m = sideif side ef.ef_ml ef.ef_mr in
        let penv, qenv = LDecl.hoareF m f hyps in
        let fmake pre post c_or_bd =
          ensure_none c_or_bd;
          f_hoareF pre f post in
        let f_true = {m; inv=f_true} in
        (penv, qenv, Inv_ss f_true, Inv_ss f_true, tbool, lift_ss_inv2 fmake)

      | FequivS es ->
        let f = sideif side es.es_sl es.es_sr in
        let m = sideif side es.es_ml es.es_mr in
        let m = (EcIdent.create "&hr", snd m) in
        let env = LDecl.push_active_ss m hyps in
        let fmake pre post c_or_bd =
          match info1, c_or_bd with
          | None, Some (PCI_bd (cmp,bd)) ->
            let cmp = odfl FHeq cmp in
            f_bdHoareS (snd m) pre f post cmp bd

          | None, None ->
            let cmp, bd = FHeq, {m=pre.m; inv=f_r1} in
            f_bdHoareS (snd m) pre f post cmp bd

          | _, None ->
            f_hoareS (snd m) pre f post

          | _, Some (PCI_bd (cmp,bd)) ->
            let cmp = odfl FHeq cmp in
            f_bdHoareS (snd m) pre f post cmp bd in
        let f_true = {m=fst m; inv=f_true} in
        (env, env, Inv_ss f_true, Inv_ss f_true, tbool, lift_ss_inv2 fmake)

      | _ -> tc_error !!tc "conseq: not a phl/prhl judgement"
    in

    let pre  = pre  |> omap (TTC.pf_process_form !!tc penv ty) |> odfl (inv_of_inv gpre)  in
    let post = post |> omap (TTC.pf_process_form !!tc qenv ty) |> odfl (inv_of_inv gpost) in

    let (pre, post, c_or_bd) = match gpre, gpost with
    | Inv_ss gpre, Inv_ss gpost ->
        let bd = c_or_bd |> omap (process_info !!tc penv gpre.m) in
        (Inv_ss {inv=pre;m=gpre.m}, Inv_ss {inv=post;m=gpost.m}, bd)
    | Inv_ts gpre, Inv_ts gpost ->
        ensure_none c_or_bd;
        (Inv_ts {inv=pre;ml=gpre.ml;mr=gpost.mr},
         Inv_ts {inv=post;ml=gpost.ml;mr=gpost.mr},
         None)
    | _ -> tc_error !!tc "conseq: pre and post must be of the same kind" in

    fmake pre post c_or_bd

  in

  if   List.for_all is_none [info1; info2; info3]
  then t_id tc
  else
    let f1 = info1 |> omap (PT.tc1_process_full_closed_pterm_cut
                              ~prcut:(process_cut1) tc) in
    let f2 = info2 |> omap (PT.tc1_process_full_closed_pterm_cut
                              ~prcut:(process_cut2 `Left f1) tc) in
    let f3 = info3 |> omap (PT.tc1_process_full_closed_pterm_cut
                              ~prcut:(process_cut2 `Right f1) tc) in

    let ofalse = omap (fun (x, y) -> (Some x, y)) in

    t_hi_conseq notmod (f1 |> ofalse) (f2 |> ofalse) (f3 |> ofalse) tc

(* -------------------------------------------------------------------- *)
let process_bd_equiv side (pr, po) tc =
  let info = FPCut ((Some pr, Some po), None) in
  let info = Some { fp_mode = `Implicit; fp_head = info; fp_args = []; } in
  let info2, info3 = sideif side (info, None) (None, info) in
  process_conseq true (None, info2, info3) tc

(* -------------------------------------------------------------------- *)
type cqpotions = {
  cqo_frame : bool;
}

module CQOptions = struct
  let default = { cqo_frame = true; }

  let merge1 opts ((b, x) : bool * EcParsetree.pcqoption) =
    match x with
    | `Frame -> { opts with cqo_frame = b; }

  let merge opts (specs : EcParsetree.pcqoptions) =
    List.fold_left merge1 opts specs
end

(* -------------------------------------------------------------------- *)
let process_conseq_opt cqopt infos tc =
  let cqopt = CQOptions.merge CQOptions.default cqopt in
  process_conseq cqopt.cqo_frame infos tc

(* -------------------------------------------------------------------- *)
let t_conseqauto ?(delta = true) ?tsolve tc =
  let (hyps, concl), mk_other = FApi.tc1_flat tc, true in

  let todo =
    match concl.f_node with
    | FhoareF hf  -> Some (lift_ss_inv t_hoareF_notmod, cond_hoareF_notmod ~mk_other tc (hf_po hf))
    | FhoareS hs  -> Some (lift_ss_inv t_hoareS_notmod, cond_hoareS_notmod ~mk_other tc (hs_po hs) )
    | FbdHoareF hf -> Some (lift_ss_inv t_bdHoareF_notmod, cond_bdHoareF_notmod ~mk_other tc (bhf_po hf))
    | FbdHoareS hs -> Some (lift_ss_inv t_bdHoareS_notmod, cond_bdHoareS_notmod ~mk_other tc (bhs_po hs))
    | FequivF ef   -> Some (lift_ts_inv t_equivF_notmod, cond_equivF_notmod ~mk_other tc (ef_po ef))
    | FequivS es   -> Some (lift_ts_inv t_equivS_notmod, cond_equivS_notmod ~mk_other tc (es_po es) )
    | _            -> None in

  match todo with
  | None ->
    tc_error_noXhl ~kinds:hlkinds_Xhl !!tc

  | Some (t_notmod, (cond, bdm, bdo)) ->
    let alln = List.map EcIdent.name (bdm @ List.map fst bdo) in
    let ids = EcEnv.LDecl.fresh_ids hyps alln in
    let ms, other = List.split_at (List.length bdm) ids in
    let tc' = EcCoreGoal.tcenv1_of_proof (EcCoreGoal.start hyps cond) in

    let rec my_intros_i (oth_bdo) tc =
      match oth_bdo with
      | [] -> t_id tc
      | (x, x') :: oth_bdo ->
        let x1 = proj3_1 (destr_forall1 (FApi.tc1_goal tc)) in
        if   EcIdent.id_equal x' x1
        then (t_intro_i x @! my_intros_i oth_bdo) tc
        else  my_intros_i oth_bdo tc
    in

    let tc' =
      FApi.t_seqs
        [ my_intros_i (List.combine ms bdm)
        ; t_crush_fwd ~delta 1
        ; my_intros_i (List.combine other (List.map fst bdo))
        ; t_crush ~delta ?tsolve ] tc' in

    let post =
      if FApi.tc_done tc' then f_true
      else
        let concl = FApi.tc_goal tc' in
        (* Build the inversion substitution *)
        let s = Fsubst.f_subst_id in
        let s = List.fold_left2 Fsubst.f_bind_mem s ms bdm in
        let s = List.fold_left2 Fsubst.f_bind_local s other (List.map (fun (bdo: _*ss_inv) -> (snd bdo).inv) bdo) in
        Fsubst.f_subst s concl in
    let post =
      match ms with
      | [m] -> Inv_ss { inv = post; m}
      | [ml; mr] -> Inv_ts { inv = post; ml; mr }
      | _ -> failwith "posts should have 1 or 2 memory parameters" in

    let t_end = FApi.t_try (t_crush ~delta ?tsolve @! t_fail) in
    FApi.t_first t_end (t_notmod post tc)
