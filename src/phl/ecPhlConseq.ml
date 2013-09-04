(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcCorePhl
open EcCoreHiPhl
open EcCoreHiLogic
open EcPV

(* -------------------------------------------------------------------- *)
class rn_hl_conseq = object
  inherit xrule "[hl] conseq"
end

class rn_hl_notmod = object
  inherit xrule "[hl] notmod"
end

(* -------------------------------------------------------------------- *)
let rn_hl_notmod = RN_xtd (new rn_hl_notmod :> xrule)
let rn_hl_conseq = RN_xtd (new rn_hl_conseq :> xrule)

(* -------------------------------------------------------------------- *)
let conseq_cond pre post spre spost =
  f_imp pre spre, f_imp spost post

let t_hoareF_conseq pre post g =
  let env,_,concl = get_goal_e g in
  let hf = t_as_hoareF concl in
  let mpr,mpo = EcEnv.Fun.hoareF_memenv hf.hf_f env in
  let cond1, cond2 = conseq_cond hf.hf_pr hf.hf_po pre post in
  let concl1 = f_forall_mems [mpr] cond1 in
  let concl2 = f_forall_mems [mpo] cond2 in
  let concl3 = f_hoareF pre hf.hf_f post in
  prove_goal_by [concl1; concl2; concl3] rn_hl_conseq g

let t_hoareS_conseq pre post g =
  let concl = get_concl g in
  let hs = t_as_hoareS concl in
  let cond1, cond2 = conseq_cond hs.hs_pr hs.hs_po pre post in
  let concl1 = f_forall_mems [hs.hs_m] cond1 in
  let concl2 = f_forall_mems [hs.hs_m] cond2 in
  let concl3 = f_hoareS_r { hs with hs_pr = pre; hs_po = post } in
  prove_goal_by [concl1; concl2; concl3] rn_hl_conseq g

let t_bdHoareF_conseq pre post g =
  let env,_,concl = get_goal_e g in
  let bhf = t_as_bdHoareF concl in
  let mpr,mpo = EcEnv.Fun.hoareF_memenv bhf.bhf_f env in
  let cond1, cond2 = conseq_cond bhf.bhf_pr bhf.bhf_po pre post in
  let cond2 = match bhf.bhf_cmp with
    | FHle -> f_imp bhf.bhf_po post
    | FHeq -> f_iff bhf.bhf_po post
    | FHge -> cond2
  in
  let concl1 = f_forall_mems [mpr] cond1 in
  let concl2 = f_forall_mems [mpo] cond2 in
  let concl3 = f_bdHoareF pre bhf.bhf_f post bhf.bhf_cmp bhf.bhf_bd in
  prove_goal_by [concl1; concl2; concl3] rn_hl_conseq g

let t_bdHoareS_conseq pre post g =
  let concl = get_concl g in
  let bhs = t_as_bdHoareS concl in
  let cond1, cond2 = conseq_cond bhs.bhs_pr bhs.bhs_po pre post in
  let cond2 = match bhs.bhs_cmp with
    | FHle -> f_imp bhs.bhs_po post
    | FHeq -> f_iff bhs.bhs_po post
    | FHge -> cond2
  in
  let concl1 = f_forall_mems [bhs.bhs_m] cond1 in
  let concl2 = f_forall_mems [bhs.bhs_m] cond2 in
  let concl3 = f_bdHoareS_r { bhs with bhs_pr = pre; bhs_po = post } in
  prove_goal_by [concl1; concl2; concl3] rn_hl_conseq g

let bd_goal fcmp fbd cmp bd =
  match fcmp, cmp with
  | FHle, (FHle | FHeq) -> f_real_le bd fbd
  | FHle, FHge -> tacuerror "can not swap comparison"
  | FHeq, FHeq -> f_eq bd fbd
  | FHeq, _ -> tacuerror "can only equality is accepted"
  | FHge, (FHge | FHeq)  -> f_real_le fbd bd
  | FHge, FHle -> tacuerror "can not swap comparison"

let t_bdHoareF_conseq_bd cmp bd g =
  let env,_,concl = get_goal_e g in
  let bhf = t_as_bdHoareF concl in
  let mpr,_ = EcEnv.Fun.hoareF_memenv bhf.bhf_f env in
  let bd_goal =  bd_goal bhf.bhf_cmp bhf.bhf_bd cmp bd in
  let concl = f_bdHoareF bhf.bhf_pr bhf.bhf_f bhf.bhf_po cmp bd in
  let bd_goal = f_forall_mems [mpr] (f_imp bhf.bhf_pr bd_goal) in
  prove_goal_by [bd_goal;concl] rn_hl_conseq g

let t_bdHoareS_conseq_bd cmp bd g =
  let concl = get_concl g in
  let bhs = t_as_bdHoareS concl in
  let bd_goal =  bd_goal bhs.bhs_cmp bhs.bhs_bd cmp bd in
  let concl = f_bdHoareS bhs.bhs_m bhs.bhs_pr bhs.bhs_s bhs.bhs_po cmp bd in
  let bd_goal = f_forall_mems [bhs.bhs_m] (f_imp bhs.bhs_pr bd_goal) in
  prove_goal_by [bd_goal;concl] rn_hl_conseq g

let t_equivF_conseq pre post g =
  let env,_,concl = get_goal_e g in
  let ef = t_as_equivF concl in
  let (mprl,mprr),(mpol,mpor) =
    EcEnv.Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
  let cond1, cond2 = conseq_cond ef.ef_pr ef.ef_po pre post in
  let concl1 = f_forall_mems [mprl;mprr] cond1 in
  let concl2 = f_forall_mems [mpol;mpor] cond2 in
  let concl3 = f_equivF pre ef.ef_fl ef.ef_fr post in
  prove_goal_by [concl1; concl2; concl3] rn_hl_conseq g

let t_equivS_conseq pre post g =
  let concl = get_concl g in
  let es = t_as_equivS concl in
  let cond1, cond2 = conseq_cond es.es_pr es.es_po pre post in
  let concl1 = f_forall_mems [es.es_ml;es.es_mr] cond1 in
  let concl2 = f_forall_mems [es.es_ml;es.es_mr] cond2 in
  let concl3 = f_equivS_r { es with es_pr = pre; es_po = post } in
  prove_goal_by [concl1; concl2; concl3] rn_hl_conseq g

let t_conseq pre post g =
  match (get_concl g).f_node with
  | FhoareF _   -> t_hoareF_conseq pre post g
  | FhoareS _   -> t_hoareS_conseq pre post g
  | FbdHoareF _ -> t_bdHoareF_conseq pre post g
  | FbdHoareS _ -> t_bdHoareS_conseq pre post g
  | FequivF _   -> t_equivF_conseq pre post g
  | FequivS _   -> t_equivS_conseq pre post g
  | _           -> tacerror (NotPhl None)

(* -------------------------------------------------------------------- *)
let t_equivF_notmod post g =
  let env,hyps,concl = get_goal_e g in
  let ef = t_as_equivF concl in
  let fl, fr = ef.ef_fl, ef.ef_fr in
  let (mprl,mprr),(mpol,mpor) = Fun.equivF_memenv fl fr env in
  let fsigl = (Fun.by_xpath fl env).f_sig in
  let fsigr = (Fun.by_xpath fr env).f_sig in
  let pvresl = pv_res fl and pvresr = pv_res fr in
  let vresl = LDecl.fresh_id hyps "result_L" in
  let vresr = LDecl.fresh_id hyps "result_R" in
  let fresl = f_local vresl fsigl.fs_ret in
  let fresr = f_local vresr fsigr.fs_ret in
  let ml, mr = fst mpol, fst mpor in
  let s = PVM.add env pvresl ml fresl (PVM.add env pvresr mr fresr PVM.empty) in
  let cond = f_imp post ef.ef_po in
  let cond = PVM.subst env s cond in
  let modil, modir = f_write env fl, f_write env fr in
  let cond = generalize_mod env mr modir cond in
  let cond = generalize_mod env ml modil cond in
  let cond =
    f_forall_simpl
      [(vresl, GTty fsigl.fs_ret);
       (vresr, GTty fsigr.fs_ret)]
      cond in
  assert (fst mprl = ml && fst mprr = mr);
  let cond1 = f_forall_mems [mprl; mprr] (f_imp ef.ef_pr cond) in
  let cond2 = f_equivF ef.ef_pr fl fr post in
  prove_goal_by [cond1;cond2] rn_hl_notmod g

let t_equivS_notmod post g =
  let env,_,concl = get_goal_e g in
  let es = t_as_equivS concl in
  let sl, sr = es.es_sl, es.es_sr in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let cond = f_imp post es.es_po in
  let modil, modir = s_write env sl, s_write env sr in
  let cond = generalize_mod env mr modir cond in
  let cond = generalize_mod env ml modil cond in
  let cond1 = f_forall_mems [es.es_ml; es.es_mr] (f_imp es.es_pr cond) in
  let cond2 = f_equivS_r {es with es_po = post} in
  prove_goal_by [cond1;cond2] rn_hl_notmod g

let t_hoareF_notmod post g =
  let env,hyps,concl = get_goal_e g in
  let hf = t_as_hoareF concl in
  let f = hf.hf_f in
  let mpr,mpo = Fun.hoareF_memenv f env in
  let fsig = (Fun.by_xpath f env).f_sig in
  let pvres = pv_res f in
  let vres = LDecl.fresh_id hyps "result" in
  let fres = f_local vres fsig.fs_ret in
  let m    = fst mpo in
  let s = PVM.add env pvres m fres PVM.empty in
  let cond = f_imp post hf.hf_po in
  let cond = PVM.subst env s cond in
  let modi = f_write env f in
  let cond = generalize_mod env m modi cond in
  let cond =
    f_forall_simpl [(vres, GTty fsig.fs_ret)] cond in
  assert (fst mpr = m);
  let cond1 = f_forall_mems [mpr] (f_imp hf.hf_pr cond) in
  let cond2 = f_hoareF hf.hf_pr f post in
  prove_goal_by [cond1;cond2] rn_hl_notmod g

let t_hoareS_notmod post g =
  let env,_,concl = get_goal_e g in
  let hs = t_as_hoareS concl in
  let s = hs.hs_s in
  let m = fst hs.hs_m in
  let cond = f_imp post hs.hs_po in
  let modi = s_write env s in
  let cond = generalize_mod env m modi cond in
  let cond1 = f_forall_mems [hs.hs_m] (f_imp hs.hs_pr cond) in
  let cond2 = f_hoareS_r {hs with hs_po = post} in
  prove_goal_by [cond1;cond2] rn_hl_notmod g

let t_bdHoareF_notmod post g =
  let env,hyps,concl = get_goal_e g in
  let hf = t_as_bdHoareF concl in
  let f = hf.bhf_f in
  let mpr,mpo = Fun.hoareF_memenv f env in
  let fsig = (Fun.by_xpath f env).f_sig in
  let pvres = pv_res f in
  let vres = LDecl.fresh_id hyps "result" in
  let fres = f_local vres fsig.fs_ret in
  let m    = fst mpo in
  let s = PVM.add env pvres m fres PVM.empty in
  let cond = f_imp post hf.bhf_po in
  let cond = PVM.subst env s cond in
  let modi = f_write env f in
  let cond = generalize_mod env m modi cond in
  let cond =
    f_forall_simpl [(vres, GTty fsig.fs_ret)] cond in
  assert (fst mpr = m);
  let cond1 = f_forall_mems [mpr] (f_imp hf.bhf_pr cond) in
  let cond2 = f_bdHoareF hf.bhf_pr f post hf.bhf_cmp hf.bhf_bd in
  prove_goal_by [cond1;cond2] rn_hl_notmod g

let t_bdHoareS_notmod post g =
  let env,_,concl = get_goal_e g in
  let hs = t_as_bdHoareS concl in
  let s = hs.bhs_s in
  let m = fst hs.bhs_m in
  let cond = f_imp post hs.bhs_po in
  let modi = s_write env s in
  let cond = generalize_mod env m modi cond in
  let cond1 = f_forall_mems [hs.bhs_m] (f_imp hs.bhs_pr cond) in
  let cond2 = f_bdHoareS_r {hs with bhs_po = post} in
  prove_goal_by [cond1;cond2] rn_hl_notmod g

(* -------------------------------------------------------------------- *)
let gen_conseq_nm tnm tc pre post =
  t_seq_subgoal (tnm post)
    [ t_id None;
      t_seq_subgoal (tc pre post)
        [t_id None; t_trivial; t_id None] ]

let t_hoareF_conseq_nm   = gen_conseq_nm t_hoareF_notmod   t_hoareF_conseq
let t_hoareS_conseq_nm   = gen_conseq_nm t_hoareS_notmod   t_hoareS_conseq
let t_equivF_conseq_nm   = gen_conseq_nm t_equivF_notmod   t_equivF_conseq
let t_equivS_conseq_nm   = gen_conseq_nm t_equivS_notmod   t_equivS_conseq
let t_bdHoareF_conseq_nm = gen_conseq_nm t_bdHoareF_notmod t_bdHoareF_conseq
let t_bdHoareS_conseq_nm = gen_conseq_nm t_bdHoareS_notmod t_bdHoareS_conseq

(* -------------------------------------------------------------------- *)
let process_conseq notmod info (_, n as g) =
  let process_cut g ((pre,post),bd) =
    let hyps,concl = get_goal g in
    let ensure_none o =
      if o <> None then tacuerror "Can not give a bound here." in
    let penv, qenv, gpre, gpost, fmake =
      match concl.f_node with
      | FhoareF hf ->
        let penv, qenv = LDecl.hoareF hf.hf_f hyps in
        penv, qenv, hf.hf_pr, hf.hf_po,
        (fun pre post bd -> ensure_none bd;f_hoareF pre hf.hf_f post)
      | FhoareS hs ->
        let env = LDecl.push_active hs.hs_m hyps in
        env, env, hs.hs_pr, hs.hs_po,
        (fun pre post bd -> ensure_none bd;f_hoareS_r { hs with hs_pr = pre; hs_po = post })
      | FbdHoareF bhf ->
        let penv, qenv = LDecl.hoareF bhf.bhf_f hyps in
        penv, qenv, bhf.bhf_pr, bhf.bhf_po,
        (fun pre post bd ->
          let cmp,bd = odfl (None,bhf.bhf_bd) bd in
          let cmp = odfl bhf.bhf_cmp cmp in
          f_bdHoareF pre bhf.bhf_f post cmp bd)
      | FbdHoareS bhs ->
        let env = LDecl.push_active bhs.bhs_m hyps in
        env, env, bhs.bhs_pr, bhs.bhs_po,
        (fun pre post bd ->
          let cmp,bd = odfl (None,bhs.bhs_bd) bd in
          let cmp = odfl bhs.bhs_cmp cmp in
          f_bdHoareS_r
            { bhs with bhs_pr = pre; bhs_po = post; bhs_cmp = cmp; bhs_bd = bd})
      | FequivF ef ->
        let penv, qenv = LDecl.equivF ef.ef_fl ef.ef_fr hyps in
        penv, qenv, ef.ef_pr, ef.ef_po,
        (fun pre post bd -> ensure_none bd;f_equivF pre ef.ef_fl ef.ef_fr post)
      | FequivS es ->
        let env = LDecl.push_all [es.es_ml; es.es_mr] hyps in
        env, env, es.es_pr, es.es_po,
        (fun pre post bd -> ensure_none bd;f_equivS_r { es with es_pr = pre; es_po = post })
      | _ -> tacuerror "cannot apply conseq rule, not a phl/prhl judgement"
    in
    let pre = match pre with
      | None -> gpre
      | Some pre -> process_form penv pre tbool in
    let post = match post with
      | None -> gpost
      | Some post -> process_form qenv post tbool in
    let bd = match bd with
      | None -> None
      | Some (cmp,bd) ->
        let bd = process_form penv bd treal in
        let cmp  = cmp |> omap (function PFHle -> FHle | PFHeq -> FHeq | PFHge -> FHge) in
        Some (cmp,bd) in
    fmake pre post bd
  in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let lt = ref [t_use an gs] in
  let t_trivial = t_try (t_lseq [t_simplify_nodelta;t_split;t_fail]) in
  let t_conseq =
    let (_,f) = get_node (juc,an) in
    match f.f_node with
    | FhoareF hf   ->
      if notmod then t_hoareF_conseq_nm hf.hf_pr hf.hf_po
      else t_hoareF_conseq hf.hf_pr hf.hf_po
    | FhoareS hs   ->
      if notmod then t_hoareS_conseq_nm hs.hs_pr hs.hs_po
      else t_hoareS_conseq hs.hs_pr hs.hs_po
    | FbdHoareF hf ->
      let t1 =
        if notmod then t_bdHoareF_conseq_nm hf.bhf_pr hf.bhf_po
        else t_bdHoareF_conseq hf.bhf_pr hf.bhf_po in
      let t2 = t_bdHoareF_conseq_bd hf.bhf_cmp hf.bhf_bd in
      lt := t_trivial :: !lt;
      t_seq_subgoal t1 [t_id None; t_id None; t2]
    | FbdHoareS hs ->
      let t1 =
        if notmod then t_bdHoareS_conseq_nm hs.bhs_pr hs.bhs_po
        else t_bdHoareS_conseq hs.bhs_pr hs.bhs_po in
      let t2 = t_bdHoareS_conseq_bd hs.bhs_cmp hs.bhs_bd in
      lt := t_trivial :: !lt;
      t_seq_subgoal t1 [t_id None; t_id None; t2]
    | FequivF ef   ->
      if notmod then t_equivF_conseq_nm ef.ef_pr ef.ef_po
      else t_equivF_conseq ef.ef_pr ef.ef_po
    | FequivS es   ->
      if notmod then t_equivS_conseq_nm es.es_pr es.es_po
      else t_equivS_conseq es.es_pr es.es_po
    | _ -> tacuerror "cannot apply conseq rule, not a phl/prhl judgement"
  in
    t_subgoal (t_trivial :: t_trivial :: !lt) (t_conseq (juc, n))
