(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let conseq_cond pre post spre spost =
  f_imp pre spre, f_imp spost post

let bd_goal_r fcmp fbd cmp bd =
  match fcmp, cmp with
  | FHle, (FHle | FHeq) -> Some (f_real_le bd fbd)
  | FHge, (FHge | FHeq) -> Some (f_real_le fbd bd)
  | FHeq, FHeq          -> Some (f_eq bd fbd)
  | _   , _             -> None

let bd_goal pe fcmp fbd cmp bd =
  match bd_goal_r fcmp fbd cmp bd with
  | None    -> tc_error pe "cannot swap"
  | Some fp -> fp

(* -------------------------------------------------------------------- *)
let t_hoareF_conseq pre post tc =
  let env = FApi.tc1_env tc in
  let hf  = tc1_as_hoareF tc in
  let mpr,mpo = EcEnv.Fun.hoareF_memenv hf.hf_f env in
  let cond1, cond2 = conseq_cond hf.hf_pr hf.hf_po pre post in
  let concl1 = f_forall_mems [mpr] cond1 in
  let concl2 = f_forall_mems [mpo] cond2 in
  let concl3 = f_hoareF pre hf.hf_f post in
  FApi.xmutate1 tc `Conseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_hoareS_conseq pre post tc =
  let hs = tc1_as_hoareS tc in
  let cond1, cond2 = conseq_cond hs.hs_pr hs.hs_po pre post in
  let concl1 = f_forall_mems [hs.hs_m] cond1 in
  let concl2 = f_forall_mems [hs.hs_m] cond2 in
  let concl3 = f_hoareS_r { hs with hs_pr = pre; hs_po = post } in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_bdHoareF_conseq pre post tc =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in
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
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_bdHoareS_conseq pre post tc =
  let bhs = tc1_as_bdhoareS tc in
  let cond1, cond2 = conseq_cond bhs.bhs_pr bhs.bhs_po pre post in
  let cond2 = match bhs.bhs_cmp with
    | FHle -> f_imp bhs.bhs_po post
    | FHeq -> f_iff bhs.bhs_po post
    | FHge -> cond2
  in
  let concl1 = f_forall_mems [bhs.bhs_m] cond1 in
  let concl2 = f_forall_mems [bhs.bhs_m] cond2 in
  let concl3 = f_bdHoareS_r { bhs with bhs_pr = pre; bhs_po = post } in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_bdHoareF_conseq_bd cmp bd tc =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in
  let mpr,_ = EcEnv.Fun.hoareF_memenv bhf.bhf_f env in
  let bd_goal =  bd_goal !!tc bhf.bhf_cmp bhf.bhf_bd cmp bd in
  let concl = f_bdHoareF bhf.bhf_pr bhf.bhf_f bhf.bhf_po cmp bd in
  let bd_goal = f_forall_mems [mpr] (f_imp bhf.bhf_pr bd_goal) in
  FApi.xmutate1 tc `HlConseq [bd_goal; concl]

(* -------------------------------------------------------------------- *)
let t_bdHoareS_conseq_bd cmp bd tc =
  let bhs = tc1_as_bdhoareS tc in
  let bd_goal = bd_goal !!tc bhs.bhs_cmp bhs.bhs_bd cmp bd in
  let concl = f_bdHoareS bhs.bhs_m bhs.bhs_pr bhs.bhs_s bhs.bhs_po cmp bd in
  let bd_goal = f_forall_mems [bhs.bhs_m] (f_imp bhs.bhs_pr bd_goal) in
  FApi.xmutate1 tc `HlConseq [bd_goal; concl]

(* -------------------------------------------------------------------- *)
let t_equivF_conseq pre post tc =
  let env = FApi.tc1_env tc in
  let ef  = tc1_as_equivF tc in
  let (mprl,mprr), (mpol,mpor) =
    EcEnv.Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
  let cond1, cond2 = conseq_cond ef.ef_pr ef.ef_po pre post in
  let concl1 = f_forall_mems [mprl;mprr] cond1 in
  let concl2 = f_forall_mems [mpol;mpor] cond2 in
  let concl3 = f_equivF pre ef.ef_fl ef.ef_fr post in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_eagerF_conseq pre post tc =
  let env = FApi.tc1_env tc in
  let eg = tc1_as_eagerF tc in
  let (mprl,mprr), (mpol,mpor) =
    EcEnv.Fun.equivF_memenv eg.eg_fl eg.eg_fr env in
  let cond1, cond2 = conseq_cond eg.eg_pr eg.eg_po pre post in
  let concl1 = f_forall_mems [mprl;mprr] cond1 in
  let concl2 = f_forall_mems [mpol;mpor] cond2 in
  let concl3 = f_eagerF pre eg.eg_sl eg.eg_fl eg.eg_fr eg.eg_sr post in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_equivS_conseq pre post tc =
  let es = tc1_as_equivS tc in
  let cond1, cond2 = conseq_cond es.es_pr es.es_po pre post in
  let concl1 = f_forall_mems [es.es_ml;es.es_mr] cond1 in
  let concl2 = f_forall_mems [es.es_ml;es.es_mr] cond2 in
  let concl3 = f_equivS_r { es with es_pr = pre; es_po = post } in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_conseq pre post tc =
  match (FApi.tc1_goal tc).f_node with
  | FhoareF _   -> t_hoareF_conseq pre post tc
  | FhoareS _   -> t_hoareS_conseq pre post tc
  | FbdHoareF _ -> t_bdHoareF_conseq pre post tc
  | FbdHoareS _ -> t_bdHoareS_conseq pre post tc
  | FequivF _   -> t_equivF_conseq pre post tc
  | FequivS _   -> t_equivS_conseq pre post tc
  | FeagerF _   -> t_eagerF_conseq pre post tc
  | _           -> tc_error_notphl !!tc None

(* -------------------------------------------------------------------- *)
let t_equivF_notmod post tc =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let ef = tc1_as_equivF tc in
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
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let t_equivS_notmod post tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let sl, sr = es.es_sl, es.es_sr in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let cond = f_imp post es.es_po in
  let modil, modir = s_write env sl, s_write env sr in
  let cond = generalize_mod env mr modir cond in
  let cond = generalize_mod env ml modil cond in
  let cond1 = f_forall_mems [es.es_ml; es.es_mr] (f_imp es.es_pr cond) in
  let cond2 = f_equivS_r {es with es_po = post} in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let t_hoareF_notmod post tc =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let hf = tc1_as_hoareF tc in
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
  let cond = f_forall_simpl [(vres, GTty fsig.fs_ret)] cond in
  assert (fst mpr = m);
  let cond1 = f_forall_mems [mpr] (f_imp hf.hf_pr cond) in
  let cond2 = f_hoareF hf.hf_pr f post in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let t_hoareS_notmod post tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_hoareS tc in
  let s = hs.hs_s in
  let m = fst hs.hs_m in
  let cond = f_imp post hs.hs_po in
  let modi = s_write env s in
  let cond = generalize_mod env m modi cond in
  let cond1 = f_forall_mems [hs.hs_m] (f_imp hs.hs_pr cond) in
  let cond2 = f_hoareS_r {hs with hs_po = post} in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let t_bdHoareF_notmod post tc =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let hf = tc1_as_bdhoareF tc in
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
  let cond = f_forall_simpl [(vres, GTty fsig.fs_ret)] cond in
  assert (fst mpr = m);
  let cond1 = f_forall_mems [mpr] (f_imp hf.bhf_pr cond) in
  let cond2 = f_bdHoareF hf.bhf_pr f post hf.bhf_cmp hf.bhf_bd in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let t_bdHoareS_notmod post tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_bdhoareS tc in
  let s = hs.bhs_s in
  let m = fst hs.bhs_m in
  let cond = f_imp post hs.bhs_po in
  let modi = s_write env s in
  let cond = generalize_mod env m modi cond in
  let cond1 = f_forall_mems [hs.bhs_m] (f_imp hs.bhs_pr cond) in
  let cond2 = f_bdHoareS_r {hs with bhs_po = post} in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let gen_conseq_nm tnm tc pre post =
  FApi.t_internal ~info:"generic-conseq-nm" (
    FApi.t_seqsub (tnm post)
      [ t_id;
        FApi.t_seqsub (tc pre post)
          [t_id; t_logic_trivial; t_id] ])

let t_hoareF_conseq_nm   = gen_conseq_nm t_hoareF_notmod   t_hoareF_conseq
let t_hoareS_conseq_nm   = gen_conseq_nm t_hoareS_notmod   t_hoareS_conseq
let t_equivF_conseq_nm   = gen_conseq_nm t_equivF_notmod   t_equivF_conseq
let t_equivS_conseq_nm   = gen_conseq_nm t_equivS_notmod   t_equivS_conseq
let t_bdHoareF_conseq_nm = gen_conseq_nm t_bdHoareF_notmod t_bdHoareF_conseq
let t_bdHoareS_conseq_nm = gen_conseq_nm t_bdHoareS_notmod t_bdHoareS_conseq

(* -------------------------------------------------------------------- *)
(*                   Relation between logics                            *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
let t_hoareS_conseq_bdhoare tc =
  let hs = tc1_as_hoareS tc in
  let concl1 = f_bdHoareS hs.hs_m hs.hs_pr hs.hs_s hs.hs_po FHeq f_r1 in
  FApi.xmutate1 tc `HlConseqBd [concl1]

(* -------------------------------------------------------------------- *)
let t_hoareF_conseq_bdhoare tc =
  let hf = tc1_as_hoareF tc in
  let concl1 = f_bdHoareF hf.hf_pr hf.hf_f hf.hf_po FHeq f_r1 in
  FApi.xmutate1 tc `HlConseqBd [concl1]

(* -------------------------------------------------------------------- *)
let t_hoareS_conseq_conj pre post pre' post' tc =
  let hs = tc1_as_hoareS tc in
  if not (f_equal hs.hs_pr (f_and pre' pre)) then
    tc_error !!tc "invalid pre-condition";
  if not (f_equal hs.hs_po (f_and post' post)) then
    tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareS_r { hs with hs_pr = pre; hs_po = post } in
  let concl2 = f_hoareS_r { hs with hs_pr = pre'; hs_po = post' } in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)
let t_hoareF_conseq_conj pre post pre' post' tc =
  let hf = tc1_as_hoareF tc in
  if not (f_equal hf.hf_pr (f_and pre' pre)) then
    tc_error !!tc "invalid pre-condition";
  if not (f_equal hf.hf_po (f_and post' post)) then
    tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareF pre hf.hf_f post in
  let concl2 = f_hoareF pre' hf.hf_f post' in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)
let t_bdHoareS_conseq_conj pre post pre' post' tc =
  let hs = tc1_as_bdhoareS tc in
  if not (f_equal hs.bhs_pr (f_and pre' pre)) then
    tc_error !!tc "invalid pre-condition";
  if not (f_equal hs.bhs_po (f_and post' post)) then
    tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareS hs.bhs_m pre hs.bhs_s post in
  let concl2 = f_bdHoareS_r {hs with bhs_pr = pre'; bhs_po = post'} in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)
let t_bdHoareF_conseq_conj pre post pre' post' tc =
  let hf = tc1_as_bdhoareF tc in
  if not (f_equal hf.bhf_pr (f_and pre' pre)) then
    tc_error !!tc "invalid pre-condition";
  if not (f_equal hf.bhf_po (f_and post' post)) then
    tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareF   pre  hf.bhf_f post in
  let concl2 = f_bdHoareF pre' hf.bhf_f post' hf.bhf_cmp hf.bhf_bd in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)
let t_equivS_conseq_conj pre1 post1 pre2 post2 pre' post' tc =
  let es = tc1_as_equivS tc in
  let subst1 = Fsubst.f_subst_mem mhr mleft in
  let subst2 = Fsubst.f_subst_mem mhr mright in
  let pre1'  = subst1 pre1 in
  let post1' = subst1 post1 in
  let pre2'  = subst2 pre2 in
  let post2' = subst2 post2 in
  if not (f_equal es.es_pr (f_ands [pre';pre1';pre2'])) then
    tc_error !!tc "invalid pre-condition";
  if not (f_equal es.es_po (f_ands [post';post1';post2'])) then
    tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareS (mhr,snd es.es_ml) pre1 es.es_sl post1 in
  let concl2 = f_hoareS (mhr,snd es.es_mr) pre2 es.es_sr post2 in
  let concl3 = f_equivS_r {es with es_pr = pre'; es_po = post'} in
  FApi.xmutate1 tc `HlConseqConj [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_equivF_conseq_conj pre1 post1 pre2 post2 pre' post' tc =
  let ef = tc1_as_equivF tc in
  let subst1 = Fsubst.f_subst_mem mhr mleft in
  let subst2 = Fsubst.f_subst_mem mhr mright in
  let pre1'  = subst1 pre1 in
  let post1' = subst1 post1 in
  let pre2'  = subst2 pre2 in
  let post2' = subst2 post2 in
  if not (f_equal ef.ef_pr (f_ands [pre';pre1';pre2']) ) then
    tc_error !!tc "invalid pre-condition";
  if not (f_equal ef.ef_po (f_ands [post';post1';post2'])) then
    tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareF pre1 ef.ef_fl post1 in
  let concl2 = f_hoareF pre2 ef.ef_fr post2 in
  let concl3 = f_equivF pre' ef.ef_fl ef.ef_fr post' in
  FApi.xmutate1 tc `HlConseqConj [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_equivS_conseq_bd side pr po tc =
  let es = tc1_as_equivS tc in
  let m,s,s' =
    if   side
    then es.es_ml, es.es_sl, es.es_sr
    else es.es_mr, es.es_sr, es.es_sl
  in
  if not (List.isempty s'.s_node) then begin
    let side = if side then "right" else "left" in
    tc_error !!tc "%s statement should be empty" side
  end;
  let subst = Fsubst.f_subst_mem mhr (fst m) in
  let prs, pos = subst pr, subst po in
  if not (f_equal prs es.es_pr && f_equal pos es.es_po) then
    tc_error !!tc "invalid pre- or post-condition";
  let g1 = f_bdHoareS m pr s po FHeq f_r1 in
  FApi.xmutate1 tc `HlBdEquiv [g1]

(* -------------------------------------------------------------------- *)
let rec t_hi_conseq notmod f1 f2 f3 tc =
  let t_trivial = [t_simplify ~delta:false; t_split; t_fail] in
  let t_trivial = FApi.t_try (FApi.t_seqs t_trivial) in
  let t_on1     = FApi.t_on1 ~ttout:t_trivial in
  let t_on1seq  = FApi.t_on1seq ~ttout:t_trivial in

  let t_apply_r (pt, _f) tc =
    match pt with
    | Some pt -> t_apply pt tc
    | None    -> EcPhlTAuto.t_hoare_true tc
  in

  let concl = FApi.tc1_goal tc in

  match concl.f_node, f1, f2, f3 with
  (* ------------------------------------------------------------------ *)
  (* hoareS / hoareS / ⊥ / ⊥                                            *)
  | FhoareS _, Some ((_, {f_node = FhoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_hoareS_conseq_nm else t_hoareS_conseq in
    t_on1 2 (t_apply_r nf1) (tac hs.hs_pr hs.hs_po tc)

  (* ------------------------------------------------------------------ *)
  (* hoare S/ hoareS / hoareS / ⊥                                       *)
  | FhoareS _,
      Some ((_, { f_node = FhoareS hs }) as nf1),
      Some ((_, f2) as nf2),
      None
    ->
    let hs2 = pf_as_hoareS !!tc f2 in
    let tac = if notmod then t_hoareS_conseq_nm else t_hoareS_conseq in

    t_on1seq 2
      (tac (f_and hs.hs_pr hs2.hs_pr) (f_and hs.hs_po hs2.hs_po))
      (FApi.t_seqsub
         (t_hoareS_conseq_conj hs2.hs_pr hs2.hs_po hs.hs_pr hs.hs_po)
         [t_apply_r nf2; t_apply_r nf1])
      tc

  (* ------------------------------------------------------------------ *)
  (* hoareS / bdhoareS / ⊥ / ⊥                                          *)
  | FhoareS _, Some ((_, {f_node = FbdHoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in

    FApi.t_seq
      t_hoareS_conseq_bdhoare
      (t_on1seq 1
         (t_bdHoareS_conseq_bd hs.bhs_cmp hs.bhs_bd)
         (t_on1seq 2 (tac hs.bhs_pr hs.bhs_po) (t_apply_r nf1)))
      tc

  (* ------------------------------------------------------------------ *)
  (* hoareF / hoareF / ⊥ / ⊥                                            *)
  | FhoareF _, Some ((_, {f_node = FhoareF hs}) as nf1), None, None ->
    let tac = if notmod then t_hoareF_conseq_nm else t_hoareF_conseq in
    t_on1 2 (t_apply_r nf1) (tac hs.hf_pr hs.hf_po tc)

  (* ------------------------------------------------------------------ *)
  (* hoareF / hoareF / hoareF / ⊥                                       *)
  | FhoareF _,
      Some ((_, {f_node = FhoareF hs}) as nf1),
      Some((_, f2) as nf2),
      None
    ->
    let hs2 = pf_as_hoareF !!tc f2 in
    let tac = if notmod then t_hoareF_conseq_nm else t_hoareF_conseq in

    t_on1seq 2
      (tac (f_and hs.hf_pr hs2.hf_pr) (f_and hs.hf_po hs2.hf_po))
      (FApi.t_seqsub
         (t_hoareF_conseq_conj hs2.hf_pr hs2.hf_po hs.hf_pr hs.hf_po)
         [t_apply_r nf2; t_apply_r nf1])
      tc

  (* ------------------------------------------------------------------ *)
  (* hoareF / bdhoareF / ⊥ / ⊥                                            *)
  | FhoareF _, Some ((_, {f_node = FbdHoareF hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareF_conseq_nm else t_bdHoareF_conseq in

    FApi.t_seq
      t_hoareF_conseq_bdhoare
      (t_on1seq 1
         (t_on1seq 2 (tac hs.bhf_pr hs.bhf_po) (t_apply_r nf1))
         (t_bdHoareF_conseq_bd hs.bhf_cmp hs.bhf_bd))
      tc

  (* ------------------------------------------------------------------ *)
  (* bdhoareS / bdhoareS / ⊥ / ⊥                                        *)
  | FbdHoareS _, Some ((_, {f_node = FbdHoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in

    t_on1seq 1
      (t_bdHoareS_conseq_bd hs.bhs_cmp hs.bhs_bd)
      (t_on1seq 2 (tac hs.bhs_pr hs.bhs_po) (t_apply_r nf1))
      tc

  (* ------------------------------------------------------------------ *)
  (* bdhoareS / bdhoareS / bdhoareS / ⊥                                 *)
  | FbdHoareS _,
      Some ((_, {f_node = FbdHoareS hs}) as nf1),
      Some ((_, f2) as nf2),
      None
    ->
    let hs2 = pf_as_hoareS !!tc f2 in
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in

    t_on1seq 1 (t_bdHoareS_conseq_bd hs.bhs_cmp hs.bhs_bd)
      (t_on1seq 2
         (tac (f_and hs.bhs_pr hs2.hs_pr) (f_and hs.bhs_po hs2.hs_po))
         (FApi.t_seqsub
            (t_bdHoareS_conseq_conj hs2.hs_pr hs2.hs_po hs.bhs_pr hs.bhs_po)
            [t_apply_r nf2; t_apply_r nf1]))
      tc

  (* ------------------------------------------------------------------ *)
  (* bdhoareF / bdhoareF / ⊥ / ⊥                                        *)
  | FbdHoareF _, Some ((_, {f_node = FbdHoareF hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareF_conseq_nm else t_bdHoareF_conseq in

    t_on1seq 1
      (t_bdHoareF_conseq_bd hs.bhf_cmp hs.bhf_bd)
      (t_on1seq 2 (tac hs.bhf_pr hs.bhf_po) (t_apply_r nf1))
      tc

  (* ------------------------------------------------------------------ *)
  (* bdhoarF / bdhoareF / bdhoareF / ⊥                                  *)
  | FbdHoareF _,
      Some ((_, {f_node = FbdHoareF hs}) as nf1),
      Some ((_, f2) as nf2),
      None
    ->
    let hs2 = pf_as_hoareF !!tc f2 in
    let tac = if notmod then t_bdHoareF_conseq_nm else t_bdHoareF_conseq in

    t_on1seq 1
      (t_bdHoareF_conseq_bd hs.bhf_cmp hs.bhf_bd)
      (t_on1seq 2
         (tac (f_and hs.bhf_pr hs2.hf_pr) (f_and hs.bhf_po hs2.hf_po))
         (FApi.t_seqsub
            (t_bdHoareF_conseq_conj hs2.hf_pr hs2.hf_po  hs.bhf_pr hs.bhf_po)
            [t_apply_r nf2; t_apply_r nf1]))
      tc

  (* ------------------------------------------------------------------ *)
  (* equivS / equivS / ⊥ / ⊥                                            *)
  | FequivS _, Some ((_, {f_node = FequivS es}) as nf1), None, None ->
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in
    t_on1 2 (t_apply_r nf1) (tac es.es_pr es.es_po tc)

  (* ------------------------------------------------------------------ *)
  (* equivS / equivS / hoareS / hoareS  *)
  | FequivS _,
      Some ((_, {f_node = FequivS es}) as nf1),
      Some ((_, f2) as nf2),
      Some ((_, f3) as nf3)
    ->
    let subst1 = Fsubst.f_subst_mem mhr mleft  in
    let subst2 = Fsubst.f_subst_mem mhr mright in
    let hs2    = pf_as_hoareS !!tc f2 in
    let hs3    = pf_as_hoareS !!tc f3 in
    let pre    = f_ands [es.es_pr; subst1 hs2.hs_pr; subst2 hs3.hs_pr] in
    let post   = f_ands [es.es_po; subst1 hs2.hs_po; subst2 hs3.hs_po] in
    let tac    = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    t_on1seq 2 (tac pre post)
      (FApi.t_seqsub
         (t_equivS_conseq_conj
            hs2.hs_pr hs2.hs_po hs3.hs_pr hs3.hs_po es.es_pr es.es_po)
         [t_apply_r nf2; t_apply_r nf3; t_apply_r nf1])
      tc

  (* ------------------------------------------------------------------ *)
  (* equivS / equivS / bdhoareS / ⊥                                     *)
  | FequivS _, Some (_, {f_node = FequivS es}), Some (_, f), None
      when is_bdHoareS f
    ->
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in
    t_on1seq 2
      (tac es.es_pr es.es_po)
      (t_hi_conseq notmod None f2 None)
      tc

  (* ------------------------------------------------------------------ *)
  (* equivS / equivS / ⊥ / bdhoareS                                     *)
  | FequivS _, Some (_, {f_node = FequivS es}), None, Some (_, f)
      when is_bdHoareS f
    ->
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in
    t_on1seq 2
      (tac es.es_pr es.es_po)
      (t_hi_conseq notmod None None f3)
      tc

  (* ------------------------------------------------------------------ *)
  (* equivS / ? / ? / ⊥                                                 *)
  | FequivS es, Some _, Some _, None ->
    let f3 = f_hoareS (mhr, snd es.es_mr) f_true es.es_sr f_true in
    t_hi_conseq notmod f1 f2 (Some (None, f3)) tc

  (* ------------------------------------------------------------------ *)
  (* equivS / ? / ⊥ / ?                                                 *)
  | FequivS es, Some _, None, Some _ ->
    let f2 = f_hoareS (mhr, snd es.es_ml) f_true es.es_sl f_true in
    t_hi_conseq notmod f1 (Some (None, f2)) f3 tc

  (* ------------------------------------------------------------------ *)
  (* equivS / ⊥ / bdhoareS / ⊥                                          *)
  | FequivS _, None, Some ((_, f2) as nf2), None ->
    let subst1 = Fsubst.f_subst_mem mhr mleft in
    let hs = pf_as_bdhoareS !!tc f2 in
    let pre, post = subst1 hs.bhs_pr, subst1 hs.bhs_po in
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

   t_on1seq 2
     (tac pre post)
     (FApi.t_seq
        (t_equivS_conseq_bd true hs.bhs_pr hs.bhs_po)
        (t_apply_r nf2))
     tc

  (* ------------------------------------------------------------------ *)
  (* equivS / ⊥ / ⊥ / bdhoareS                                          *)
  | FequivS _, None, None, Some ((_, f3) as nf3) ->
    let subst2 = Fsubst.f_subst_mem mhr mright in
    let hs = pf_as_bdhoareS !!tc f3 in
    let pre, post = subst2 hs.bhs_pr, subst2 hs.bhs_po in
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    t_on1seq 2
      (tac pre post)
      (FApi.t_seq
         (t_equivS_conseq_bd false hs.bhs_pr hs.bhs_po)
         (t_apply_r nf3))
      tc

  (* ------------------------------------------------------------------ *)
  (* equivF / equivF / ⊥ / ⊥                                            *)
  | FequivF _, Some ((_, {f_node = FequivF ef}) as nf1), None, None ->
    let tac = if notmod then t_equivF_conseq_nm else t_equivF_conseq in
    t_on1seq 2 (tac ef.ef_pr ef.ef_po) (t_apply_r nf1) tc

  (* ------------------------------------------------------------------ *)
  (* equivF / equivF / hoareF / hoareF                                  *)
  | FequivF _,
      Some ((_, {f_node = FequivF ef}) as nf1),
      Some ((_, f2) as nf2),
      Some ((_, f3) as nf3)
    ->
    let subst1 = Fsubst.f_subst_mem mhr mleft in
    let subst2 = Fsubst.f_subst_mem mhr mright in
    let hs2    = pf_as_hoareF !!tc f2 in
    let hs3    = pf_as_hoareF !!tc f3 in
    let pre    = f_ands [ef.ef_pr; subst1 hs2.hf_pr; subst2 hs3.hf_pr] in
    let post   = f_ands [ef.ef_po; subst1 hs2.hf_po; subst2 hs3.hf_po] in
    let tac    = if notmod then t_equivF_conseq_nm else t_equivF_conseq in

    t_on1seq 2
      (tac pre post)
      (FApi.t_seqsub
         (t_equivF_conseq_conj
            hs2.hf_pr hs2.hf_po hs3.hf_pr hs3.hf_po ef.ef_pr ef.ef_po)
         [t_apply_r nf2; t_apply_r nf3; t_apply_r nf1])
      tc

  (* ------------------------------------------------------------------ *)
  (* equivF / ? / ? / ⊥                                                 *)
  | FequivF ef, Some _, Some _, None ->
    let f3 = f_hoareF f_true ef.ef_fr f_true in
    t_hi_conseq notmod f1 f2 (Some (None, f3)) tc

  (* ------------------------------------------------------------------ *)
  (* equivF / ? / ⊥ / ?                                                 *)
  | FequivF ef, Some _, None, Some _ ->
    let f2 = f_hoareF f_true ef.ef_fl f_true in
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
let process_conseq notmod (info1, info2, info3) tc =
  let hyps, concl = FApi.tc1_flat tc in

  let ensure_none o =
    if not (is_none o) then tc_error !!tc "cannot give a bound here" in

  let process_cut1 ((pre, post), bd) =
     let penv, qenv, gpre, gpost, fmake =
      match concl.f_node with
      | FhoareS hs ->
        let env = LDecl.push_active hs.hs_m hyps in
        let fmake pre post bd =
          match bd with
          | None -> f_hoareS_r { hs with hs_pr = pre; hs_po = post; }
          | Some (cmp, bd) -> f_bdHoareS hs.hs_m pre hs.hs_s post (oget cmp) bd
        in (env, env, hs.hs_pr, hs.hs_po, fmake)

      | FhoareF hf ->
        let penv, qenv = LDecl.hoareF hf.hf_f hyps in
        let fmake pre post bd =
          match bd with
          | None -> f_hoareF pre hf.hf_f post
          | Some (cmp, bd) -> f_bdHoareF pre hf.hf_f post (oget cmp) bd
        in (penv, qenv, hf.hf_pr, hf.hf_po, fmake)

      | FbdHoareS bhs ->
        let env = LDecl.push_active bhs.bhs_m hyps in
        let fmake pre post bd =
          let cmp,bd = odfl (None, bhs.bhs_bd) bd in
          let cmp = odfl bhs.bhs_cmp cmp in
          f_bdHoareS_r { bhs with
            bhs_pr = pre; bhs_po = post; bhs_cmp = cmp; bhs_bd = bd; }
        in (env, env, bhs.bhs_pr, bhs.bhs_po, fmake)

      | FbdHoareF hf ->
        let penv, qenv = LDecl.hoareF hf.bhf_f hyps in
        let fmake pre post bd =
          let cmp, bd = bd |> odfl (None, hf.bhf_bd) in
          let cmp = cmp |> odfl hf.bhf_cmp in
          f_bdHoareF pre hf.bhf_f post cmp bd
        in (penv, qenv, hf.bhf_pr, hf.bhf_po, fmake)

      | FequivF ef ->
        let penv, qenv = LDecl.equivF ef.ef_fl ef.ef_fr hyps in
        let fmake pre post bd =
          ensure_none bd; f_equivF pre ef.ef_fl ef.ef_fr post
        in (penv, qenv, ef.ef_pr, ef.ef_po, fmake)

      | FequivS es ->
        let env = LDecl.push_all [es.es_ml; es.es_mr] hyps in
        let fmake pre post bd =
          ensure_none bd; f_equivS_r { es with es_pr = pre; es_po = post; }
        in (env, env, es.es_pr, es.es_po, fmake)

      | _ -> tc_error !!tc "conseq: not a phl/prhl judgement"
    in

    let pre  = pre  |> omap (TTC.pf_process_formula !!tc penv) |> odfl gpre  in
    let post = post |> omap (TTC.pf_process_formula !!tc qenv) |> odfl gpost in
    let bd   = bd   |> omap (snd_map (TTC.pf_process_form !!tc penv treal)) in

    fmake pre post bd

  in

  let process_cut2 side ((pre, post), bd) =
    let penv, qenv, gpre, gpost, fmake =
      match concl.f_node with
      | FhoareS hs ->
        let env = LDecl.push_active hs.hs_m hyps in
        let fmake pre post bd =
          ensure_none bd; f_hoareS_r { hs with hs_pr = pre; hs_po = post; }
        in (env, env, hs.hs_pr, hs.hs_po, fmake)

      | FhoareF hf ->
        let penv, qenv = LDecl.hoareF hf.hf_f hyps in
        let fmake pre post bd = ensure_none bd; f_hoareF pre hf.hf_f post in
        (penv, qenv, hf.hf_pr, hf.hf_po, fmake)

      | FbdHoareS bhs ->
        let env = LDecl.push_active bhs.bhs_m hyps in
        let fmake pre post bd =
          ensure_none bd; f_hoareS bhs.bhs_m pre bhs.bhs_s post
        in (env, env, bhs.bhs_pr, bhs.bhs_po, fmake)

      | FequivF ef ->
        let f = if side then ef.ef_fl else ef.ef_fr in
        let penv, qenv = LDecl.hoareF f hyps in
        let fmake pre post bd = ensure_none bd; f_hoareF pre f post in
        (penv, qenv, f_true, f_true, fmake)

      | FequivS es ->
        let f = if side then es.es_sl else es.es_sr in
        let m = if side then es.es_ml else es.es_mr in
        let env = LDecl.push_active m hyps in
        let fmake pre post bd =
          match info1, bd with
          | None, _ ->
            let cmp, bd = odfl (None, f_r1) bd in
            let cmp = odfl FHeq cmp in
              f_bdHoareS m pre f post cmp bd

          | _, None ->
            f_hoareS m pre f post

          | _, Some (cmp, bd) ->
            let cmp = odfl FHeq cmp in
              f_bdHoareS m pre f post cmp bd
        in (env, env, f_true, f_true, fmake)

      | _ -> tc_error !!tc "conseq: not a phl/prhl judgement"
    in

    let pre  = pre  |> omap (TTC.pf_process_formula !!tc penv) |> odfl gpre  in
    let post = post |> omap (TTC.pf_process_formula !!tc qenv) |> odfl gpost in
    let bd   = bd   |> omap (snd_map (TTC.pf_process_form !!tc penv treal)) in

    fmake pre post bd

  in

  if   List.for_all is_none [info1; info2; info3]
  then t_id tc
  else
    let f1 = info1 |> omap (PT.tc1_process_full_closed_pterm_cut ~prcut:(process_cut1      ) tc) in
    let f2 = info2 |> omap (PT.tc1_process_full_closed_pterm_cut ~prcut:(process_cut2 true ) tc) in
    let f3 = info3 |> omap (PT.tc1_process_full_closed_pterm_cut ~prcut:(process_cut2 false) tc) in

    let ofalse = omap (fun (x, y) -> (Some x, y)) in

    t_hi_conseq notmod (f1 |> ofalse) (f2 |> ofalse) (f3 |> ofalse) tc

(* -------------------------------------------------------------------- *)
let process_bd_equiv side (pr, po) tc =
  let info = Some { fp_kind = FPCut ((Some pr, Some po),None); fp_args = [] } in
  let info2, info3 = if side then info, None else None, info in
  process_conseq true (None, info2, info3) tc
