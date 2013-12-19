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
  | FHeq, _ -> tacuerror "only equality is accepted"
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

let t_eagerF_conseq pre post g =
  let env,_,concl = get_goal_e g in
  let eg = t_as_eagerF concl in
  let (mprl,mprr),(mpol,mpor) =
    EcEnv.Fun.equivF_memenv eg.eg_fl eg.eg_fr env in
  let cond1, cond2 = conseq_cond eg.eg_pr eg.eg_po pre post in
  let concl1 = f_forall_mems [mprl;mprr] cond1 in
  let concl2 = f_forall_mems [mpol;mpor] cond2 in
  let concl3 = f_eagerF pre eg.eg_sl eg.eg_fl eg.eg_fr eg.eg_sr post in
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
  | FeagerF _   -> t_eagerF_conseq pre post g
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
        [t_id None; t_logic_trivial; t_id None] ]

let t_hoareF_conseq_nm   = gen_conseq_nm t_hoareF_notmod   t_hoareF_conseq
let t_hoareS_conseq_nm   = gen_conseq_nm t_hoareS_notmod   t_hoareS_conseq
let t_equivF_conseq_nm   = gen_conseq_nm t_equivF_notmod   t_equivF_conseq
let t_equivS_conseq_nm   = gen_conseq_nm t_equivS_notmod   t_equivS_conseq
let t_bdHoareF_conseq_nm = gen_conseq_nm t_bdHoareF_notmod t_bdHoareF_conseq
let t_bdHoareS_conseq_nm = gen_conseq_nm t_bdHoareS_notmod t_bdHoareS_conseq

(* -------------------------------------------------------------------- *)
(*                   Relation between logics                            *)
(* phoare [c : P ==> Q] = 1 
   -------------------------
     hoare [c:P ==> Q] *)

(* Remark the rule 
   hoare [c:P ==> Q] <=> phoare[c:P ==> !Q] = 0 
   is defined else where tactic hoare *)

(*     phoare[c:P ==> Q] = 1 
  ----------------------------------
      equiv[c ~ [] : P{1} ==> Q{1}] 
    implemented elsewhere
*)

class rn_hl_conseq_bd = object
  inherit xrule "[hl] conseq bd"
end

let rn_hl_conseq_bd = RN_xtd (new rn_hl_conseq_bd :> xrule)

let t_hoareS_conseq_bdhoare g = 
  let concl = get_concl g in
  let hs = t_as_hoareS concl in
  let concl1 = f_bdHoareS hs.hs_m hs.hs_pr hs.hs_s hs.hs_po FHeq f_r1 in
  prove_goal_by [concl1] rn_hl_conseq_bd g

let t_hoareF_conseq_bdhoare g = 
  let concl = get_concl g in
  let hf = t_as_hoareF concl in
  let concl1 = f_bdHoareF hf.hf_pr hf.hf_f hf.hf_po FHeq f_r1 in
  prove_goal_by [concl1] rn_hl_conseq_bd g


class rn_hl_conseq_conj = object
  inherit xrule "[hl] conseq bd"
end

let rn_hl_conseq_conj = RN_xtd (new rn_hl_conseq_conj :> xrule)

(* hoare[c:P => Q]    hoare[c:P' => Q']
   -----------------------------------------
      hoare[c:P /\ P' ==> Q /\ Q' ] *)

(* hoare[c:P => Q]    phoare[c:P' => Q'] ? d
   -----------------------------------------
      phoare[c:P /\ P' ==> Q /\ Q' ] ? d *)

(* hoare[c1:P1 => Q1] hoare[c2:P2 ==> Q2]    equiv[c1 ~ c2 :P => Q] 
   -----------------------------------------------------------------
    equiv[c1 ~ c2 : P /\ P1{1} /\ P2{2} ==> Q /\ Q1{1} /\ Q2{2} ] *)

let t_hoareS_conseq_conj pre post pre' post' g = 
  let concl = get_concl g in
  let hs = t_as_hoareS concl in
  if not (f_equal hs.hs_pr (f_and pre' pre) ) then
    tacuerror "bad pre condition";
  if not (f_equal hs.hs_po (f_and post' post)) then
    tacuerror "bad post condition";
  let concl1 = f_hoareS_r {hs with hs_pr = pre; hs_po = post} in
  let concl2 = f_hoareS_r {hs with hs_pr = pre'; hs_po = post'} in
  prove_goal_by [concl1;concl2] rn_hl_conseq_conj g

let t_hoareF_conseq_conj pre post pre' post' g = 
  let concl = get_concl g in
  let hf = t_as_hoareF concl in
  if not (f_equal hf.hf_pr (f_and pre' pre) ) then
    tacuerror "bad pre condition";
  if not (f_equal hf.hf_po (f_and post' post)) then
    tacuerror "bad post condition";
  let concl1 = f_hoareF pre hf.hf_f post in
  let concl2 = f_hoareF pre' hf.hf_f post' in
  prove_goal_by [concl1;concl2] rn_hl_conseq_conj g

let t_bdHoareS_conseq_conj pre post pre' post' g = 
  let concl = get_concl g in
  let hs = t_as_bdHoareS concl in
  if not (f_equal hs.bhs_pr (f_and pre' pre) ) then
    tacuerror "bad pre condition";
  if not (f_equal hs.bhs_po (f_and post' post)) then
    tacuerror "bad post condition";
  let concl1 = f_hoareS hs.bhs_m pre hs.bhs_s post in
  let concl2 = f_bdHoareS_r {hs with bhs_pr = pre'; bhs_po = post'} in
  prove_goal_by [concl1;concl2] rn_hl_conseq_conj g

let t_bdHoareF_conseq_conj pre post pre' post' g = 
  let concl = get_concl g in
  let hf = t_as_bdHoareF concl in
  if not (f_equal hf.bhf_pr (f_and pre' pre) ) then
    tacuerror "bad pre condition";
  if not (f_equal hf.bhf_po (f_and post' post)) then
    tacuerror "bad post condition";
  let concl1 = f_hoareF   pre  hf.bhf_f post in
  let concl2 = f_bdHoareF pre' hf.bhf_f post' hf.bhf_cmp hf.bhf_bd in
  prove_goal_by [concl1;concl2] rn_hl_conseq_conj g
 
let t_equivS_conseq_conj pre1 post1 pre2 post2 pre' post' g = 
  let concl = get_concl g in
  let es = t_as_equivS concl in
  let subst1 = Fsubst.f_subst_mem mhr mleft in
  let subst2 = Fsubst.f_subst_mem mhr mright in
  let pre1'  = subst1 pre1 in
  let post1' = subst1 post1 in
  let pre2'  = subst2 pre2 in
  let post2' = subst2 post2 in
  if not (f_equal es.es_pr (f_ands [pre';pre1';pre2']) ) then
    tacuerror "bad pre condition";
  if not (f_equal es.es_po (f_ands [post';post1';post2'])) then
    tacuerror "bad post condition";
  let concl1 = f_hoareS (mhr,snd es.es_ml) pre1 es.es_sl post1 in
  let concl2 = f_hoareS (mhr,snd es.es_mr) pre2 es.es_sr post2 in
  let concl3 = f_equivS_r {es with es_pr = pre'; es_po = post'} in
  prove_goal_by [concl1;concl2;concl3] rn_hl_conseq_conj g

let t_equivF_conseq_conj pre1 post1 pre2 post2 pre' post' g = 
  let concl = get_concl g in
  let ef = t_as_equivF concl in
  let subst1 = Fsubst.f_subst_mem mhr mleft in
  let subst2 = Fsubst.f_subst_mem mhr mright in
  let pre1'  = subst1 pre1 in
  let post1' = subst1 post1 in
  let pre2'  = subst2 pre2 in
  let post2' = subst2 post2 in
  if not (f_equal ef.ef_pr (f_ands [pre';pre1';pre2']) ) then
    tacuerror "bad pre condition";
  if not (f_equal ef.ef_po (f_ands [post';post1';post2'])) then
    tacuerror "bad post condition";
  let concl1 = f_hoareF pre1 ef.ef_fl post1 in
  let concl2 = f_hoareF pre2 ef.ef_fr post2 in
  let concl3 = f_equivF pre' ef.ef_fl ef.ef_fr post' in
  prove_goal_by [concl1;concl2;concl3] rn_hl_conseq_conj g

(* deduce equiv from phoare *)
class rn_hl_bd_equiv = object
  inherit xrule "[hl] bd equiv"
end
let rn_hl_bd_equiv = RN_xtd (new rn_hl_bd_equiv :> xrule)

let t_equivS_conseq_bd side pr po g = 
  let concl = get_concl g in
  let es = destr_equivS concl in
  let m,s,s' = 
    if side then es.es_ml, es.es_sl,es.es_sr 
    else es.es_mr, es.es_sr, es.es_sl in
  if s'.s_node <> [] then 
    tacuerror "%s statement should be empty"
      (if side then "right" else "left");
  
  let subst = Fsubst.f_subst_mem mhr (fst m) in
  let prs, pos = subst pr, subst po in
  if not (f_equal prs es.es_pr && f_equal pos es.es_po) then
    tacuerror "invalid pre or post condition";
  let g1 = f_bdHoareS m pr s po FHeq f_r1 in
  prove_goal_by [g1] rn_hl_bd_equiv g



let rec t_hi_conseq notmod f1 f2 f3 g =
  let t_use (n,gs)= t_use n gs in
  let hyps,concl = get_goal g in

  let t_trivial = t_try (t_lseq [t_simplify_nodelta;t_split;t_fail]) in
  match concl.f_node, f1, f2, f3 with
  | FhoareS _, Some(nf1,{f_node = FhoareS hs}), None, None ->
    let tac = if notmod then t_hoareS_conseq_nm else t_hoareS_conseq in
    t_seq_subgoal (tac hs.hs_pr hs.hs_po) 
      [t_trivial; t_trivial; t_use nf1] g
  | FhoareS _, Some(nf1,{f_node = FhoareS hs}), Some(nf2,f2), None ->
    let hs2 = t_as_hoareS f2 in
    let tac = if notmod then t_hoareS_conseq_nm else t_hoareS_conseq in
    t_seq_subgoal (tac (f_and hs.hs_pr hs2.hs_pr) (f_and hs.hs_po hs2.hs_po))
      [t_trivial; t_trivial; 
       t_seq_subgoal 
         (t_hoareS_conseq_conj hs2.hs_pr hs2.hs_po hs.hs_pr hs.hs_po)
         [t_use nf2; t_use nf1]] g
  | FhoareS _, Some(nf1,{f_node = FbdHoareS hs}), None, None ->
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in
    t_seq t_hoareS_conseq_bdhoare
      (t_seq_subgoal (t_bdHoareS_conseq_bd hs.bhs_cmp hs.bhs_bd)
         [t_trivial;
          t_seq_subgoal (tac hs.bhs_pr hs.bhs_po)
            [t_trivial; t_trivial; t_use nf1]]) g

  | FhoareF _, Some(nf1,{f_node = FhoareF hs}), None, None ->
    let tac = if notmod then t_hoareF_conseq_nm else t_hoareF_conseq in
    t_seq_subgoal (tac hs.hf_pr hs.hf_po) 
      [t_trivial; t_trivial; t_use nf1] g
  | FhoareF _, Some(nf1,{f_node = FhoareF hs}), Some(nf2,f2), None ->
    let hs2 = t_as_hoareF f2 in
    let tac = if notmod then t_hoareF_conseq_nm else t_hoareF_conseq in
    t_seq_subgoal (tac (f_and hs.hf_pr hs2.hf_pr) (f_and hs.hf_po hs2.hf_po))
      [t_trivial; t_trivial; 
       t_seq_subgoal 
         (t_hoareS_conseq_conj hs2.hf_pr hs2.hf_po hs.hf_pr hs.hf_po)
         [t_use nf2; t_use nf1]] g
  | FhoareF _, Some(nf1,{f_node = FbdHoareF hs}), None, None ->
    let tac = if notmod then t_bdHoareF_conseq_nm else t_bdHoareF_conseq in
    t_seq t_hoareF_conseq_bdhoare 
      (t_seq_subgoal (t_bdHoareF_conseq_bd hs.bhf_cmp hs.bhf_bd)
         [t_trivial;
          t_seq_subgoal (tac hs.bhf_pr hs.bhf_po)
            [t_trivial; t_trivial; t_use nf1]]) g


  | FbdHoareS _, Some(nf1,{f_node = FbdHoareS hs}), None, None ->
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in
    t_seq_subgoal (t_bdHoareS_conseq_bd hs.bhs_cmp hs.bhs_bd)
      [t_trivial;
       t_seq_subgoal (tac hs.bhs_pr hs.bhs_po)
         [t_trivial; t_trivial; t_use nf1]] g

  | FbdHoareS _, Some(nf1,{f_node = FbdHoareS hs}), Some(nf2,f2), None -> 
    let hs2 = t_as_hoareS f2 in
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in
    t_seq_subgoal (t_bdHoareS_conseq_bd hs.bhs_cmp hs.bhs_bd)
      [t_trivial;
       t_seq_subgoal (tac (f_and hs.bhs_pr hs2.hs_pr) 
                          (f_and hs.bhs_po hs2.hs_po))
         [t_trivial; t_trivial; 
          t_seq_subgoal (t_bdHoareS_conseq_conj hs2.hs_pr hs2.hs_po 
                           hs.bhs_pr hs.bhs_po)
            [t_use nf2; t_use nf1]]] g

  | FbdHoareF _, Some(nf1,{f_node = FbdHoareF hs}), None, None ->
    let tac = if notmod then t_bdHoareF_conseq_nm else t_bdHoareF_conseq in
    t_seq_subgoal (t_bdHoareF_conseq_bd hs.bhf_cmp hs.bhf_bd)
      [t_trivial;
       t_seq_subgoal (tac hs.bhf_pr hs.bhf_po)
         [t_trivial; t_trivial; t_use nf1]] g

  | FbdHoareF _, Some(nf1,{f_node = FbdHoareF hs}), Some(nf2,f2), None -> 
    let hs2 = t_as_hoareF f2 in
    let tac = if notmod then t_bdHoareF_conseq_nm else t_bdHoareF_conseq in
    t_seq_subgoal (t_bdHoareF_conseq_bd hs.bhf_cmp hs.bhf_bd)
      [t_trivial;
       t_seq_subgoal (tac (f_and hs.bhf_pr hs2.hf_pr) 
                          (f_and hs.bhf_po hs2.hf_po))
         [t_trivial; t_trivial; 
          t_seq_subgoal (t_bdHoareF_conseq_conj hs2.hf_pr hs2.hf_po 
                           hs.bhf_pr hs.bhf_po)
            [t_use nf2; t_use nf1]]] g

  | FequivS _, Some (nf1, {f_node = FequivS es}), None, None ->
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in
    t_seq_subgoal (tac es.es_pr es.es_po) 
      [t_trivial; t_trivial; t_use nf1] g
  | FequivS _, Some(nf1,{f_node = FequivS es}), Some (nf2,f2), Some (nf3,f3) ->
    let subst1 = Fsubst.f_subst_mem mhr mleft in
    let subst2 = Fsubst.f_subst_mem mhr mright in
    let hs2, hs3 = t_as_hoareS f2, t_as_hoareS f3 in
    let pre = f_ands [es.es_pr; subst1 hs2.hs_pr; subst2 hs3.hs_pr] in
    let post = f_ands [es.es_po; subst1 hs2.hs_po; subst2 hs3.hs_po] in
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in
    t_seq_subgoal (tac pre post) 
      [ t_trivial;
        t_trivial;
        t_seq_subgoal
          (t_equivS_conseq_conj hs2.hs_pr hs2.hs_po hs3.hs_pr hs3.hs_po
             es.es_pr es.es_po)
          [t_use nf2; t_use nf3; t_use nf1]
      ] g

  | FequivS _, Some((nf1,_),{f_node = FequivS es}), Some (_,f), None when is_bdHoareS f ->
    let _ = get_goal (fst g, nf1) in
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in
    t_seq_subgoal (tac es.es_pr es.es_po) 
      [t_trivial; t_trivial; t_hi_conseq notmod None f2 None] g
  | FequivS _, Some((nf1,_),{f_node = FequivS es}), None, Some (_,f) when is_bdHoareS f ->
    let _ = get_goal (fst g, nf1) in
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in
    t_seq_subgoal (tac es.es_pr es.es_po) 
      [t_trivial; t_trivial; t_hi_conseq notmod None None f3] g

  | FequivS es, Some _, Some _, None ->
    let (juc,n) = g in
    let f3 = f_hoareS (mhr, snd es.es_mr) f_true es.es_sr f_true in
    let (juc,n3) = EcLogic.new_goal juc (hyps, f3) in
    let (juc,gs) = EcPhlTauto.t_hoare_true (juc,n3) in
    t_hi_conseq notmod f1 f2 (Some((n3,gs),f3)) (juc,n)
  | FequivS es, Some _, None, Some _ ->
    let (juc,n) = g in
    let f2 = f_hoareS (mhr, snd es.es_ml) f_true es.es_sl f_true in
    let (juc,n2) = EcLogic.new_goal juc (hyps, f2) in
    let (juc,gs) = EcPhlTauto.t_hoare_true (juc,n2) in
    t_hi_conseq notmod f1 (Some((n2,gs),f2)) f3 (juc,n)

  | FequivS _, None, Some(n2,f2), None ->
    let subst1 = Fsubst.f_subst_mem mhr mleft in
    let hs = t_as_bdHoareS f2 in
    let pre, post = subst1 hs.bhs_pr, subst1 hs.bhs_po in
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in
    t_seq_subgoal (tac pre post)
      [t_trivial;
       t_trivial;
       t_seq (t_equivS_conseq_bd true hs.bhs_pr hs.bhs_po) (t_use n2)] g
  | FequivS _, None, None, Some (n3,f3) ->
    let subst2 = Fsubst.f_subst_mem mhr mright in
    let hs = t_as_bdHoareS f3 in
    let pre, post = subst2 hs.bhs_pr, subst2 hs.bhs_po in
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in
    t_seq_subgoal (tac pre post)
      [t_trivial;
       t_trivial;
       t_seq (t_equivS_conseq_bd false hs.bhs_pr hs.bhs_po) (t_use n3)] g

  | FequivF _, Some(nf1,{f_node = FequivF ef}), None, None ->
    let tac = if notmod then t_equivF_conseq_nm else t_equivF_conseq in
    t_seq_subgoal (tac ef.ef_pr ef.ef_po)
      [t_trivial; t_trivial; t_use nf1] g

  | FequivF _, Some(nf1,{f_node = FequivF ef}), Some (nf2,f2), Some (nf3,f3) ->
    let subst1 = Fsubst.f_subst_mem mhr mleft in
    let subst2 = Fsubst.f_subst_mem mhr mright in
    let hs2, hs3 = t_as_hoareF f2, t_as_hoareF f3 in
    let pre = f_ands [ef.ef_pr; subst1 hs2.hf_pr; subst2 hs3.hf_pr] in
    let post = f_ands [ef.ef_po; subst1 hs2.hf_po; subst2 hs3.hf_po] in
    let tac = if notmod then t_equivF_conseq_nm else t_equivF_conseq in
    t_seq_subgoal (tac pre post) 
      [ t_trivial;
        t_trivial;
        t_seq_subgoal
          (t_equivF_conseq_conj hs2.hf_pr hs2.hf_po hs3.hf_pr hs3.hf_po
             ef.ef_pr ef.ef_po)
          [t_use nf2; t_use nf3; t_use nf1]
      ] g
  | FequivF ef, Some _, Some _, None ->
    let (juc,n) = g in
    let f3 = f_hoareF f_true ef.ef_fr f_true in
    let (juc,n3) = EcLogic.new_goal juc (hyps, f3) in
    let (juc,gs) = EcPhlTauto.t_hoare_true (juc,n3) in
    t_hi_conseq notmod f1 f2 (Some((n3,gs),f3)) (juc,n)
  | FequivF ef, Some _, None, Some _ ->
    let (juc,n) = g in
    let f2 = f_hoareF f_true ef.ef_fl f_true in
    let (juc,n2) = EcLogic.new_goal juc (hyps, f2) in
    let (juc,gs) = EcPhlTauto.t_hoare_true (juc,n2) in
    t_hi_conseq notmod f1 (Some((n2,gs),f2)) f3 (juc,n)
  | _ -> 
    let pp_f f = 
      match f.f_node with
      | FequivF _ -> "equivF"
      | FequivS _ -> "equivS"
      | FhoareF _ -> "hoareF"
      | FhoareS _ -> "hoareS"
      | FbdHoareF _ -> "phoareF"
      | FbdHoareS _ -> "phoareS"
      | _ -> "?" in
    let pp_o f = 
      match f with
      | None -> "_"
      | Some (_,f) -> pp_f f in
    tacuerror "do not how to combine %s and %s and %s into %s"
       (pp_o f1) (pp_o f2) (pp_o f3) (pp_f concl)

let t_infer_conseq (juc, _ as g) =
  let env, hyps, concl = get_goal_e g in
  let pre, ms, po = 
    match concl.f_node with
    | FhoareF hf -> 
      let _, mp = EcEnv.Fun.hoareF_memenv hf.hf_f env in
      hf.hf_pr, [mp], hf.hf_po 
    | FhoareS hs -> hs.hs_pr, [hs.hs_m], hs.hs_po
    | FbdHoareF hf -> 
      let _, mp = EcEnv.Fun.hoareF_memenv hf.bhf_f env in
      hf.bhf_pr, [mp], hf.bhf_po
    | FbdHoareS hs -> hs.bhs_pr, [hs.bhs_m], hs.bhs_po
    | FequivF ef ->
      let _,(mpl, mpr) =  EcEnv.Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
      ef.ef_pr, [mpl; mpr], ef.ef_po
    | FequivS es -> es.es_pr, [es.es_ml; es.es_mr], es.es_po
    | _ -> tacuerror "Do not known what to do" in
  let ids = 
    LDecl.fresh_ids hyps (List.map (fun (id,_) -> EcIdent.name id) ms) in
  let subst = 
    List.fold_left2 (fun s id (id',_) -> Fsubst.f_bind_mem s id id')
      Fsubst.f_subst_id ids ms in
  let po = f_forall_mems ms po in
  let g' = new_goal juc (hyps, po) in
  let (juc', gs) = t_intros_i ids g' in
  let g' = (juc', List.hd gs) in
  let hyps',concl' = get_goal g' in
  let (id,f), tac1 = t_build g' in
  let po = Fsubst.f_subst subst f in
  let po = EcReduction.simplify EcReduction.nodelta hyps' po in
  t_seq_subgoal (t_conseq pre po)
    [t_true;
     t_lseq [t_intros_i ids; t_change (f_imp f concl');t_intros_i [id]; tac1];
     t_id None] g

(* TODO : this code is borring it should be factorized *)
let t_infer_conseq_notmod (juc, _ as g) = 
  let env, hyps, concl = get_goal_e g in
  match concl.f_node with
  | FhoareS hs ->
    let m = fst hs.hs_m in
    let modi = s_write env hs.hs_s in
    let po,bg,bv = generalize_mod_ env m modi hs.hs_po in
    let cond = f_forall_mems [hs.hs_m] (f_imp hs.hs_pr po) in
    let g' = new_goal juc (hyps, cond) in
    let rename (l1,l2) = List.map (fun (_,x) -> EcIdent.create "_", x) l1, l2 in
    let bg = rename bg and bv = rename bv in
    let ids = List.map fst (fst bg) @ List.map fst (fst bv) in
    let m' = EcIdent.create "_" in
    let h = EcIdent.create "_" in
    let (juc,gs) = t_intros_i (m'::h::ids) g' in
    let g' = (juc, List.hd gs) in
    let hyps1, post1 = get_goal g' in
    let (juc,gs) = 
      t_lseq [t_generalize_hyp h;t_clear (EcIdent.Sid.singleton h);
              t_intros_elim 1] g' in
    let (id,f), tac = t_build (juc,List.hd gs) in
    let subst = Fsubst.f_subst_id in
    let subst = Fsubst.f_bind_mem subst m' m in
    let bindg m subst (id,_) mp =
      Fsubst.f_bind_local subst id (f_glob mp m) in
    let bindv m subst (id,_) (pv,ty) =
      Fsubst.f_bind_local subst id (f_pvar pv ty m) in
    let subst = List.fold_left2 (bindv m) subst (fst bv) (snd bv) in
    let subst = List.fold_left2 (bindg m) subst (fst bg) (snd bg) in
    let po' = Fsubst.f_subst subst f in
    let spo' = EcReduction.simplify EcReduction.nodelta hyps1 po' in
    t_seq_subgoal (t_hoareS_notmod spo')
      [t_lseq [
        t_intros_i (m'::h::ids);
         t_change (f_imp f post1);
         t_intros_i [id];
         t_generalize_hyp h;t_clear (EcIdent.Sid.singleton h);
         t_intros_elim 1;
         tac];
       t_id None ] g

  | FhoareF hf ->
    let f = hf.hf_f in
    let mpr, mpo = Fun.hoareF_memenv f env in
    let fsig = (Fun.by_xpath f env).f_sig in
    let pvres = pv_res f in
    let vres = LDecl.fresh_id hyps "result" in
    let fres = f_local vres fsig.fs_ret in
    let m = fst mpo in
    let s = PVM.add env pvres m fres PVM.empty in
    let cond = PVM.subst env s hf.hf_po in
    let modi = f_write env f in
    let cond,bg,bv = generalize_mod_ env m modi cond in
    let cond =f_forall [(vres, GTty fsig.fs_ret)] cond in
    assert (fst mpr = m);
    let cond = f_forall_mems [mpr] (f_imp hf.hf_pr cond) in
    let g' = new_goal juc (hyps, cond) in
    let rename (l1,l2) = List.map (fun (_,x) -> EcIdent.create "_", x) l1, l2 in
    let bg = rename bg and bv = rename bv in
    let ids = List.map fst (fst bg) @ List.map fst (fst bv) in
    let m' = EcIdent.create "_" in
    let h = EcIdent.create "_" in
    let (juc,gs) = t_intros_i (m'::h::vres::ids) g' in
    let g' = (juc,List.hd gs) in
    let hyps1,post1 = get_goal g' in
    let (juc,gs) = 
      t_lseq [t_generalize_hyp h;t_clear (EcIdent.Sid.singleton h);
              t_intros_elim 1] g' in
    let (id,f), tac = t_build (juc,List.hd gs) in
    let subst = Fsubst.f_subst_id in
    let subst = Fsubst.f_bind_mem subst m' m in
    let bindg m subst (id,_) mp =
      Fsubst.f_bind_local subst id (f_glob mp m) in
    let bindv m subst (id,_) (pv,ty) =
      Fsubst.f_bind_local subst id (f_pvar pv ty m) in
    let subst = List.fold_left2 (bindv m) subst (fst bv) (snd bv) in
    let subst = List.fold_left2 (bindg m) subst (fst bg) (snd bg) in
    let subst = Fsubst.f_bind_local subst vres (f_pvar pvres fsig.fs_ret m) in
    let po' = Fsubst.f_subst subst f in
    let spo' = EcReduction.simplify EcReduction.nodelta hyps1 po' in
    (* Unsure that parameters do not occur in the new post *)
    let check_res pv _ =
      if is_loc pv then
        let xp = pv.pv_name in
        if EcPath.basename (xp.EcPath.x_sub) <> "res" then
          tacuerror "Sorry: infered postcondition use parameter %a" 
            (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps)))
            spo' in
    PV.iter check_res (fun _ -> ()) (PV.fv env m spo');
    t_seq_subgoal (t_equivF_notmod spo')
      [t_lseq [
         t_intros_i (m'::h::vres::ids);
         t_change (f_imp f post1);
         t_intros_i [id];
         t_generalize_hyp h;t_clear (EcIdent.Sid.singleton h);
         t_intros_elim 1;
         tac];
       t_id None ] g

  | FbdHoareS hs ->
    let m = fst hs.bhs_m in
    let modi = s_write env hs.bhs_s in
    let po,bg,bv = generalize_mod_ env m modi hs.bhs_po in
    let cond = f_forall_mems [hs.bhs_m] (f_imp hs.bhs_pr po) in
    let g' = new_goal juc (hyps, cond) in
    let rename (l1,l2) = List.map (fun (_,x) -> EcIdent.create "_", x) l1, l2 in
    let bg = rename bg and bv = rename bv in
    let ids = List.map fst (fst bg) @ List.map fst (fst bv) in
    let m' = EcIdent.create "_" in
    let h = EcIdent.create "_" in
    let (juc,gs) = t_intros_i (m'::h::ids) g' in
    let g' = (juc, List.hd gs) in
    let hyps1, post1 = get_goal g' in
    let (juc,gs) = 
      t_lseq [t_generalize_hyp h;t_clear (EcIdent.Sid.singleton h);
              t_intros_elim 1] g' in
    let (id,f), tac = t_build (juc,List.hd gs) in
    let subst = Fsubst.f_subst_id in
    let subst = Fsubst.f_bind_mem subst m' m in
    let bindg m subst (id,_) mp =
      Fsubst.f_bind_local subst id (f_glob mp m) in
    let bindv m subst (id,_) (pv,ty) =
      Fsubst.f_bind_local subst id (f_pvar pv ty m) in
    let subst = List.fold_left2 (bindv m) subst (fst bv) (snd bv) in
    let subst = List.fold_left2 (bindg m) subst (fst bg) (snd bg) in
    let po' = Fsubst.f_subst subst f in
    let spo' = EcReduction.simplify EcReduction.nodelta hyps1 po' in
    t_seq_subgoal (t_hoareS_notmod spo')
      [t_lseq [
        t_intros_i (m'::h::ids);
         t_change (f_imp f post1);
         t_intros_i [id];
         t_generalize_hyp h;t_clear (EcIdent.Sid.singleton h);
         t_intros_elim 1;
         tac];
       t_id None ] g

  | FbdHoareF hf ->
    let f = hf.bhf_f in
    let mpr, mpo = Fun.hoareF_memenv f env in
    let fsig = (Fun.by_xpath f env).f_sig in
    let pvres = pv_res f in
    let vres = LDecl.fresh_id hyps "result" in
    let fres = f_local vres fsig.fs_ret in
    let m = fst mpo in
    let s = PVM.add env pvres m fres PVM.empty in
    let cond = PVM.subst env s hf.bhf_po in
    let modi = f_write env f in
    let cond,bg,bv = generalize_mod_ env m modi cond in
    let cond =f_forall [(vres, GTty fsig.fs_ret)] cond in
    assert (fst mpr = m);
    let cond = f_forall_mems [mpr] (f_imp hf.bhf_pr cond) in
    let g' = new_goal juc (hyps, cond) in
    let rename (l1,l2) = List.map (fun (_,x) -> EcIdent.create "_", x) l1, l2 in
    let bg = rename bg and bv = rename bv in
    let ids = List.map fst (fst bg) @ List.map fst (fst bv) in
    let m' = EcIdent.create "_" in
    let h = EcIdent.create "_" in
    let (juc,gs) = t_intros_i (m'::h::vres::ids) g' in
    let g' = (juc,List.hd gs) in
    let hyps1,post1 = get_goal g' in
    let (juc,gs) = 
      t_lseq [t_generalize_hyp h;t_clear (EcIdent.Sid.singleton h);
              t_intros_elim 1] g' in
    let (id,f), tac = t_build (juc,List.hd gs) in
    let subst = Fsubst.f_subst_id in
    let subst = Fsubst.f_bind_mem subst m' m in
    let bindg m subst (id,_) mp =
      Fsubst.f_bind_local subst id (f_glob mp m) in
    let bindv m subst (id,_) (pv,ty) =
      Fsubst.f_bind_local subst id (f_pvar pv ty m) in
    let subst = List.fold_left2 (bindv m) subst (fst bv) (snd bv) in
    let subst = List.fold_left2 (bindg m) subst (fst bg) (snd bg) in
    let subst = Fsubst.f_bind_local subst vres (f_pvar pvres fsig.fs_ret m) in
    let po' = Fsubst.f_subst subst f in
    let spo' = EcReduction.simplify EcReduction.nodelta hyps1 po' in
    (* Unsure that parameters do not occur in the new post *)
    let check_res pv _ =
      if is_loc pv then
        let xp = pv.pv_name in
        if EcPath.basename (xp.EcPath.x_sub) <> "res" then
          tacuerror "Sorry: infered postcondition use parameter %a" 
            (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps)))
            spo' in
    PV.iter check_res (fun _ -> ()) (PV.fv env m spo');
    t_seq_subgoal (t_equivF_notmod spo')
      [t_lseq [
         t_intros_i (m'::h::vres::ids);
         t_change (f_imp f post1);
         t_intros_i [id];
         t_generalize_hyp h;t_clear (EcIdent.Sid.singleton h);
         t_intros_elim 1;
         tac];
       t_id None ] g
 
  | FequivS es ->
    let ml, mr = fst es.es_ml, fst es.es_mr in    
    let modil, modir = s_write env es.es_sl, s_write env es.es_sr in
    let po,bgr,bvr = generalize_mod_ env mr modir es.es_po in
    let po,bgl,bvl = generalize_mod_ env ml modil po in
    let cond = f_forall_mems [es.es_ml; es.es_mr] (f_imp es.es_pr po) in
    let g' = new_goal juc (hyps, cond) in
    let rename (l1,l2) = List.map (fun (_,x) -> EcIdent.create "_", x) l1, l2 in
    let bgr = rename bgr and bgl = rename bgl in
    let bvr = rename bvr and bvl = rename bvl in
    let ids =
      List.map fst (fst bgl) @ List.map fst (fst bvl) @
        List.map fst (fst bgr) @ List.map fst (fst bvr) in
    let ml', mr' = EcIdent.create "_", EcIdent.create "_" in
    let h = EcIdent.create "_" in
    let (juc,gs) = t_intros_i (ml'::mr'::h::ids) g' in
    let g' = (juc, List.hd gs) in
    let hyps1, post1 = get_goal g' in
    let (juc,gs) = 
      t_lseq [t_generalize_hyp h;t_clear (EcIdent.Sid.singleton h);
              t_intros_elim 1] g' in
    let (id,f), tac = t_build (juc,List.hd gs) in
    let subst = Fsubst.f_subst_id in
    let subst = Fsubst.f_bind_mem (Fsubst.f_bind_mem subst ml' ml) mr' mr in
    let bindg m subst (id,_) mp =
      Fsubst.f_bind_local subst id (f_glob mp m) in
    let bindv m subst (id,_) (pv,ty) =
      Fsubst.f_bind_local subst id (f_pvar pv ty m) in
    let subst = List.fold_left2 (bindv mr) subst (fst bvr) (snd bvr) in
    let subst = List.fold_left2 (bindv ml) subst (fst bvl) (snd bvl) in
    let subst = List.fold_left2 (bindg mr) subst (fst bgr) (snd bgr) in
    let subst = List.fold_left2 (bindg ml) subst (fst bgl) (snd bgl) in
    let po' = Fsubst.f_subst subst f in
    let spo' = EcReduction.simplify EcReduction.nodelta hyps1 po' in
    t_seq_subgoal (t_equivS_notmod spo')
      [t_lseq [
        t_intros_i (ml'::mr'::h::ids);
         t_change (f_imp f post1);
         t_intros_i [id];
         t_generalize_hyp h;t_clear (EcIdent.Sid.singleton h);
         t_intros_elim 1;
         tac];
       t_id None ] g
  | FequivF ef ->
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
    let s = 
      PVM.add env pvresl ml fresl (PVM.add env pvresr mr fresr PVM.empty) in
    let cond = PVM.subst env s ef.ef_po in
    let modil, modir = f_write env fl, f_write env fr in
    let cond,bgr,bvr = generalize_mod_ env mr modir cond in
    let cond,bgl,bvl = generalize_mod_ env ml modil cond in
    let cond =
      f_forall
        [(vresl, GTty fsigl.fs_ret);
         (vresr, GTty fsigr.fs_ret)]
        cond in
    assert (fst mprl = ml && fst mprr = mr);
    let cond = f_forall_mems [mprl; mprr] (f_imp ef.ef_pr cond) in
    let g' = new_goal juc (hyps, cond) in
    let rename (l1,l2) = List.map (fun (_,x) -> EcIdent.create "_", x) l1, l2 in
    let bgr = rename bgr and bgl = rename bgl in
    let bvr = rename bvr and bvl = rename bvl in
    let ids =
      List.map fst (fst bgl) @ List.map fst (fst bvl) @
        List.map fst (fst bgr) @ List.map fst (fst bvr) in
    let ml', mr' = EcIdent.create "_", EcIdent.create "_" in
    let h = EcIdent.create "_" in
    let (juc,gs) = t_intros_i (ml'::mr'::h::vresl::vresr::ids) g' in
    let g' = (juc,List.hd gs) in
    let hyps1,post1 = get_goal g' in
    let (juc,gs) = 
      t_lseq [t_generalize_hyp h;t_clear (EcIdent.Sid.singleton h);
              t_intros_elim 1] g' in
    let (id,f), tac = t_build (juc,List.hd gs) in
    let subst = Fsubst.f_subst_id in
    let subst = Fsubst.f_bind_mem (Fsubst.f_bind_mem subst ml' ml) mr' mr in
    let bindg m subst (id,_) mp =
      Fsubst.f_bind_local subst id (f_glob mp m) in
    let bindv m subst (id,_) (pv,ty) =
      Fsubst.f_bind_local subst id (f_pvar pv ty m) in
    let subst = List.fold_left2 (bindv mr) subst (fst bvr) (snd bvr) in
    let subst = List.fold_left2 (bindv ml) subst (fst bvl) (snd bvl) in
    let subst = List.fold_left2 (bindg mr) subst (fst bgr) (snd bgr) in
    let subst = List.fold_left2 (bindg ml) subst (fst bgl) (snd bgl) in
    let subst = 
      Fsubst.f_bind_local subst vresl (f_pvar pvresl fsigl.fs_ret ml) in
    let subst = 
      Fsubst.f_bind_local subst vresr (f_pvar pvresr fsigr.fs_ret mr) in
    let po' = Fsubst.f_subst subst f in
    let spo' = EcReduction.simplify EcReduction.nodelta hyps1 po' in
    (* Unsure that parameters do not occur in the new post *)
    let check_res pv _ =
      if is_loc pv then
        let xp = pv.pv_name in
        if EcPath.basename (xp.EcPath.x_sub) <> "res" then
          tacuerror "Sorry: infered postcondition use parameter %a" 
            (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps)))
            spo' in
    PV.iter check_res (fun _ -> ()) (PV.fv env ml spo');
    PV.iter check_res (fun _ -> ()) (PV.fv env mr spo');
    t_seq_subgoal (t_equivF_notmod spo')
      [t_lseq [
         t_intros_i (ml'::mr'::h::vresl::vresr::ids);
         t_change (f_imp f post1);
         t_intros_i [id];
         t_generalize_hyp h;t_clear (EcIdent.Sid.singleton h);
         t_intros_elim 1;
         tac];
       t_id None ] g

  | _ -> tacuerror "Do not known what to do" 


         
         
              

  


(* -------------------------------------------------------------------- *)
let process_conseq notmod (info1,info2,info3) (juc, n as g) =
  let hyps,concl = get_goal g in
  let ensure_none o =
    if o <> None then tacuerror "Can not give a bound here." in

  let process_cut1 ((pre,post),bd) =
     let penv, qenv, gpre, gpost, fmake =
      match concl.f_node with
      | FhoareS hs ->
        let env = LDecl.push_active hs.hs_m hyps in
        env, env, hs.hs_pr, hs.hs_po,
        (fun pre post bd -> 
          match bd with
          | None ->f_hoareS_r { hs with hs_pr = pre; hs_po = post }
          | Some(cmp,bd) -> f_bdHoareS hs.hs_m pre hs.hs_s post (oget cmp) bd)
      | FhoareF hf ->
        let penv, qenv = LDecl.hoareF hf.hf_f hyps in
        penv, qenv, hf.hf_pr, hf.hf_po,
        (fun pre post bd -> 
          match bd with
          | None -> f_hoareF pre hf.hf_f post
          | Some(cmp,bd) -> f_bdHoareF pre hf.hf_f post (oget cmp) bd)
      | FbdHoareS bhs ->
        let env = LDecl.push_active bhs.bhs_m hyps in
        env, env, bhs.bhs_pr, bhs.bhs_po,
        (fun pre post bd ->
          let cmp,bd = odfl (None, bhs.bhs_bd) bd in
          let cmp = odfl bhs.bhs_cmp cmp in
          f_bdHoareS_r
            { bhs with bhs_pr = pre; bhs_po = post; bhs_cmp = cmp; bhs_bd = bd})
      | FbdHoareF hf ->
        let penv, qenv = LDecl.hoareF hf.bhf_f hyps in
        penv, qenv, hf.bhf_pr, hf.bhf_po,
        (fun pre post bd -> 
          let cmp,bd = odfl (None, hf.bhf_bd) bd in
          let cmp = odfl hf.bhf_cmp cmp in
          f_bdHoareF pre hf.bhf_f post cmp bd)
      | FequivF ef ->
        let penv, qenv = LDecl.equivF ef.ef_fl ef.ef_fr hyps in
        penv, qenv, ef.ef_pr, ef.ef_po,
        (fun pre post bd -> 
          ensure_none bd;f_equivF pre ef.ef_fl ef.ef_fr post)
      | FequivS es ->
        let env = LDecl.push_all [es.es_ml; es.es_mr] hyps in
        env, env, es.es_pr, es.es_po,
        (fun pre post bd -> 
          ensure_none bd;
          f_equivS_r { es with es_pr = pre; es_po = post })
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

  let process_cut2 side ((pre,post),bd) =
    let penv, qenv, gpre, gpost, fmake =
      match concl.f_node with
      | FhoareS hs ->
        let env = LDecl.push_active hs.hs_m hyps in
        env, env, hs.hs_pr, hs.hs_po,
        (fun pre post bd -> 
          ensure_none bd;f_hoareS_r { hs with hs_pr = pre; hs_po = post })
      | FhoareF hf ->
        let penv, qenv = LDecl.hoareF hf.hf_f hyps in
        penv, qenv, hf.hf_pr, hf.hf_po,
        (fun pre post bd -> 
          ensure_none bd;f_hoareF pre hf.hf_f post)
      | FbdHoareS bhs ->
        let env = LDecl.push_active bhs.bhs_m hyps in
        env, env, bhs.bhs_pr, bhs.bhs_po,
        (fun pre post bd -> 
          ensure_none bd;f_hoareS bhs.bhs_m pre bhs.bhs_s post)
      | FequivF ef ->
        let f = if side then ef.ef_fl else ef.ef_fr in
        let penv,qenv = LDecl.hoareF f hyps in
        penv, qenv, f_true, f_true, (* TODO can we improve this ? *)
        (fun pre post bd -> 
          ensure_none bd;f_hoareF pre f post)
      | FequivS es ->
        let f = if side then es.es_sl else es.es_sr in
        let m = if side then es.es_ml else es.es_mr in
        let env = LDecl.push_active m hyps in
        env, env, f_true, f_true, (* TODO can we improve this ? *)
        (fun pre post bd ->
          match info1, bd with
          | None, _ ->
            let cmp,bd = odfl (None, f_r1) bd in
            let cmp = odfl FHeq cmp in 
            f_bdHoareS m pre f post cmp bd
          | _, None -> f_hoareS m pre f post
          | _, Some (cmp,bd) ->
            let cmp = odfl FHeq cmp in 
            f_bdHoareS m pre f post cmp bd)
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

  if info1 = None && info2 = None && info3 = None then
    if notmod then t_infer_conseq_notmod g else t_infer_conseq g
  else
    let juc, f1 = 
      match info1 with
      | None -> juc, None
      | Some info ->
        let (juc,nf1), gs1 = process_mkn_apply process_cut1 info g in
        let _, f1 = get_node (juc,nf1) in  
        juc, Some ((nf1,gs1), f1) in
    let juc, f2 = 
      match info2 with
      | None -> juc, None
      | Some info ->
        let (juc,nf2), gs2 = 
          process_mkn_apply (process_cut2 true) info (juc,n) in
        let _, f2 = get_node (juc,nf2) in
        juc, Some ((nf2,gs2), f2) in
    let juc, f3 = 
      match info3 with
      | None -> juc, None
      | Some info ->
        let (juc,nf3), gs3 = 
          process_mkn_apply (process_cut2 false) info (juc,n) in
        let _, f3 = get_node (juc,nf3) in
        juc, Some ((nf3,gs3), f3) in
    t_hi_conseq notmod f1 f2 f3 (juc,n)
      
