(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
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

type conseq_tac = form -> form -> FApi.backward
type qconseq_tac =
  form -> ?qepr:quantum_equality ->
  form -> ?qepo:quantum_equality ->
  FApi.backward

type qconseq_core_tac = equiv_cond -> equiv_cond -> FApi.backward
(* -------------------------------------------------------------------- *)
let conseq_cond ?eqpr ?eqpo pre post spre spost =
  let spre = omap_dfl (f_and_simpl spre) spre eqpr in
  let post = omap_dfl (f_and_simpl post) post eqpo in
  f_imp pre spre, f_imp spost post


(*
{ sF } c { sf }  sF <= F  f <= sf
--------------------------------------------------------------------
{ F } c { f }
 *)
let conseq_econd pre post spre spost =
  f_xreal_le spre pre, f_xreal_le post spost

let qe_implies env qe1 qe2 =
  is_qe_empty qe2 ||
  EcReduction.EqTest.for_qe env ~norm:true qe1 qe2 ||
  EcQuantum.has_iso env qe1 qe2

let cond_eq_conseq_qe env ml mr qe1 qe2 =
  assert (qe1.qeg = qe2.qeg);
  let (r1l, q1l), (r1r, q1r) = EcQuantum.destr_qr_pair qe1.qel, EcQuantum.destr_qr_pair qe1.qer in
  let (r2l, q2l), (r2r, q2r) = EcQuantum.destr_qr_pair qe2.qel, EcQuantum.destr_qr_pair qe2.qer in
  assert (EcReduction.EqTest.for_qr env ~norm:true r1l r2l);
  assert (EcReduction.EqTest.for_qr env ~norm:true r1r r2r);
  let f1l = form_of_qr env q1l (fst ml) in
  let f1r = form_of_qr env q1r (fst mr) in
  let f2l = form_of_qr env q2l (fst ml) in
  let f2r = form_of_qr env q2r (fst mr) in
  assert (EcReduction.EqTest.for_type env f1l.f_ty f1r.f_ty);
  assert (EcReduction.EqTest.for_type env f2l.f_ty f2r.f_ty);
  f_and_simpl (f_eq_simpl f1l f1r) (f_eq_simpl f2l f2r)

(*
     P => q1 = q2 /\ q1' = q2'
     -----------------------------------------------
     P, (r1, q1 = r2, q2) |=> P, (r1, q1' = r2, q2')
               qe1                       qe2
*)
let qe_implies_cond ?(witheq=true) tc ml mr qe1 qe2 =
  let env = FApi.tc1_env tc in
  if qe_implies env qe1 qe2 then None
  else
    if not witheq || qe1.qeg <> qe2.qeg then
      begin
        let open EcPrinting in
          let ppe = PPEnv.ofenv (FApi.tc1_env tc) in
            tc_error !!tc ~who:"conseq" "@[not able to prove@ %a@ implies@ %a@]"
              (pp_qe ppe) qe1 (pp_qe ppe) qe2;
      end
    else
      let qe1', qe2' = EcQuantum.build_partial_iso env qe1 qe2 in
      EcQuantum.ensure_iso ~who:"conseq" tc qe1 qe1';
      EcQuantum.ensure_iso ~who:"conseq" tc qe2 qe2';
      Some (cond_eq_conseq_qe env ml mr qe1' qe2')

let conseq_eqcond ?witheq tc mprl mprr mpol mpor pre post spre spost =
  let eqpr = qe_implies_cond ?witheq tc mprl mprr pre.ec_e spre.ec_e in
  let eqpo = qe_implies_cond ?witheq tc mpol mpor spost.ec_e post.ec_e in
  conseq_cond ?eqpr ?eqpo pre.ec_f post.ec_f spre.ec_f spost.ec_f

let bd_goal_r fcmp fbd cmp bd =
  match fcmp, cmp with
  | FHle, (FHle | FHeq) -> Some (f_real_le bd fbd)
  | FHge, (FHge | FHeq) -> Some (f_real_le fbd bd)
  | FHeq, FHeq          -> Some (f_eq bd fbd)
  | FHeq, FHge          -> Some (f_and (f_eq fbd f_r1) (f_eq bd f_r1))
  | FHeq, FHle          -> Some (f_and (f_eq fbd f_r0) (f_eq bd f_r0))
  | _   , _             -> None

let bd_goal tc fcmp fbd cmp bd =
  match bd_goal_r fcmp fbd cmp bd with
  | None    ->
    let ppe = EcPrinting.PPEnv.ofenv (FApi.tc1_env tc) in
    tc_error !!tc
      "do not know how to change phoare[...]%s %a into phoare[...]%s %a"
      (EcPrinting.string_of_hcmp fcmp) (EcPrinting.pp_form ppe) fbd
      (EcPrinting.string_of_hcmp cmp) (EcPrinting.pp_form ppe) bd
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
let t_ehoareF_conseq pre post tc =
  let env = FApi.tc1_env tc in
  let hf  = tc1_as_ehoareF tc in
  let mpr,mpo = EcEnv.Fun.hoareF_memenv hf.ehf_f env in
  let cond1, cond2 =
    conseq_econd hf.ehf_pr hf.ehf_po pre post in
  let concl1 = f_forall_mems [mpr] cond1 in
  let concl2 = f_forall_mems [mpo] cond2 in
  let concl3 = f_eHoareF pre hf.ehf_f post in
  FApi.xmutate1 tc `Conseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_ehoareS_conseq pre post tc =
  let hs = tc1_as_ehoareS tc in
  let cond1, cond2 =
    conseq_econd hs.ehs_pr hs.ehs_po pre post in
  let concl1 = f_forall_mems [hs.ehs_m] cond1 in
  let concl2 = f_forall_mems [hs.ehs_m] cond2 in
  let concl3 = f_eHoareS_r { hs with ehs_pr = pre; ehs_po = post; } in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let bdHoare_conseq_conds cmp pr po new_pr new_po =
  let cond1, cond2 = conseq_cond pr po new_pr new_po in
  let cond2 = match cmp with
    | FHle -> f_imp po new_po
    | FHeq -> f_iff po new_po
    | FHge -> cond2
  in
  cond1, cond2

let t_bdHoareF_conseq pre post tc =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in
  let mpr,mpo = EcEnv.Fun.hoareF_memenv bhf.bhf_f env in
  let cond1, cond2 =
    bdHoare_conseq_conds bhf.bhf_cmp bhf.bhf_pr bhf.bhf_po pre post in
  let concl1 = f_forall_mems [mpr] cond1 in
  let concl2 = f_forall_mems [mpo] cond2 in
  let concl3 = f_bdHoareF pre bhf.bhf_f post bhf.bhf_cmp bhf.bhf_bd in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_bdHoareS_conseq pre post tc =
  let bhs = tc1_as_bdhoareS tc in
  let cond1, cond2 =
    bdHoare_conseq_conds bhs.bhs_cmp bhs.bhs_pr bhs.bhs_po pre post in
  let concl1 = f_forall_mems [bhs.bhs_m] cond1 in
  let concl2 = f_forall_mems [bhs.bhs_m] cond2 in
  let concl3 = f_bdHoareS_r { bhs with bhs_pr = pre; bhs_po = post } in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_bdHoareF_conseq_bd cmp bd tc =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in
  let mpr,_ = EcEnv.Fun.hoareF_memenv bhf.bhf_f env in
  let bd_goal =  bd_goal tc bhf.bhf_cmp bhf.bhf_bd cmp bd in
  let concl = f_bdHoareF bhf.bhf_pr bhf.bhf_f bhf.bhf_po cmp bd in
  let bd_goal = f_forall_mems [mpr] (f_imp bhf.bhf_pr bd_goal) in
  FApi.xmutate1 tc `HlConseq [bd_goal; concl]

(* -------------------------------------------------------------------- *)
let t_bdHoareS_conseq_bd cmp bd tc =
  let bhs = tc1_as_bdhoareS tc in
  let bd_goal = bd_goal tc bhs.bhs_cmp bhs.bhs_bd cmp bd in
  let concl = f_bdHoareS bhs.bhs_m bhs.bhs_pr bhs.bhs_s bhs.bhs_po cmp bd in
  let bd_goal = f_forall_mems [bhs.bhs_m] (f_imp bhs.bhs_pr bd_goal) in
  FApi.xmutate1 tc `HlConseq [bd_goal; concl]

(* -------------------------------------------------------------------- *)
let t_equivF_conseq_core pre post tc =
  let env = FApi.tc1_env tc in
  let ef  = tc1_as_qequivF tc in
  let (mprl,mprr), (mpol,mpor) =
    EcEnv.Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
  let cond1, cond2 = conseq_eqcond tc mprl mprr mpol mpor ef.ef_pr ef.ef_po pre post in
  let concl1 = f_forall_mems [mprl;mprr] cond1 in
  let concl2 = f_forall_mems [mpol;mpor] cond2 in
  let concl3 = f_qequivF pre ef.ef_fl ef.ef_fr post in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

let ec_dfl f ?(qe=None) dfl =
  { ec_f = f; ec_e = odfl dfl.ec_e qe }

let t_equivF_conseq pre ?qepr post ?qepo tc =
  let ef  = tc1_as_qequivF tc in
  let pre, post = ec_dfl pre ~qe:qepr ef.ef_pr, ec_dfl post ~qe:qepo ef.ef_po in
  t_equivF_conseq_core pre post tc


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
let t_equivS_conseq_core ?witheq pre post tc =
  let es = tc1_as_qequivS tc in
  let ml, mr = es.es_ml, es.es_mr in
  let cond1, cond2 =
    conseq_eqcond ?witheq tc ml mr ml mr es.es_pr es.es_po pre post in
  let concl1 = f_forall_mems [ml;mr] cond1 in
  let concl2 = f_forall_mems [ml;mr] cond2 in
  let concl3 = f_qequivS_r { es with es_pr = pre; es_po = post } in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

let t_equivS_conseq pre ?qepr post ?qepo tc =
  let es = tc1_as_qequivS tc in
  let pre, post = ec_dfl pre ~qe:qepr es.es_pr, ec_dfl post ~qe:qepo es.es_po in
  t_equivS_conseq_core pre post tc

(* -------------------------------------------------------------------- *)
let t_conseq pre post tc =
  match (FApi.tc1_goal tc).f_node with
  | FhoareF _   -> t_hoareF_conseq pre post tc
  | FhoareS _   -> t_hoareS_conseq pre post tc
  | FbdHoareF _ -> t_bdHoareF_conseq pre post tc
  | FbdHoareS _ -> t_bdHoareS_conseq pre post tc
  | FeHoareF _  -> t_ehoareF_conseq pre post tc
  | FeHoareS _  -> t_ehoareS_conseq pre post tc
  | FequivF _   -> t_equivF_conseq pre post tc
  | FequivS _   -> t_equivS_conseq pre post tc
  | FeagerF _   -> t_eagerF_conseq pre post tc
  | _           -> tc_error_noXhl !!tc

(* -------------------------------------------------------------------- *)
let mk_bind_pvar m (id,_) (x, ty) = id, f_pvar x ty m
let mk_bind_glob env m (id,_) x = id, NormMp.norm_glob env m x
let mk_bind_pvars m (bd1,bd2) = List.map2 (mk_bind_pvar m) bd1 bd2
let mk_bind_globs env m (bd1,bd2) = List.map2 (mk_bind_glob env m) bd1 bd2

let cond_equivF_notmod ?(mk_other=false) tc cond =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let ef = tc1_as_qequivF tc in
  let fl, fr = ef.ef_fl, ef.ef_fr in
  let (mprl,mprr),(mpol,mpor) = Fun.equivF_memenv fl fr env in
  let fsigl = (Fun.by_xpath fl env).f_sig in
  let fsigr = (Fun.by_xpath fr env).f_sig in
  let pvresl = pv_res and pvresr = pv_res in
  let vresl = LDecl.fresh_id hyps "result_L" in
  let vresr = LDecl.fresh_id hyps "result_R" in
  let fresl = f_local vresl fsigl.fs_ret in
  let fresr = f_local vresr fsigr.fs_ret in
  let ml, mr = fst mpol, fst mpor in
  let s = PVM.add env pvresl ml fresl (PVM.add env pvresr mr fresr PVM.empty) in
  let cond = PVM.subst env s cond in
  let modil, modir = f_write env fl, f_write env fr in
  let cond, bdgr, bder = generalize_mod_ env mr modir cond in
  let cond, bdgl, bdel = generalize_mod_ env ml modil cond in
  let cond =
    f_forall_simpl
      [(vresl, GTty fsigl.fs_ret);
       (vresr, GTty fsigr.fs_ret)]
      cond in
  assert (fst mprl = ml && fst mprr = mr);
  let cond = f_forall_mems [mprl; mprr] (f_imp ef.ef_pr.ec_f cond) in
  let bmem = [ml;mr] in
  let bother =
    if mk_other then
      mk_bind_pvar ml (vresl,()) (pvresl, fsigl.fs_ret) ::
      mk_bind_pvar mr (vresr,()) (pvresr, fsigr.fs_ret) ::
      List.flatten [mk_bind_globs env ml bdgl; mk_bind_pvars ml bdel;
                    mk_bind_globs env mr bdgr; mk_bind_pvars mr bder]
    else [] in
  cond, bmem, bother

let t_equivF_notmod_core post tc =
  let ef = tc1_as_qequivF tc in
  let (mprl,mprr), (mpol,mpor) =
    EcEnv.Fun.equivF_memenv ef.ef_fl ef.ef_fr (FApi.tc1_env tc) in
  let _, condp = conseq_eqcond tc mprl mprr mpol mpor ef.ef_pr ef.ef_po ef.ef_pr post in
  let cond1, _, _ = cond_equivF_notmod tc condp in
  let cond2 = f_qequivF_r {ef with ef_po = post} in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

let t_equivF_notmod post ?qepo tc =
  let ef = tc1_as_qequivF tc in
  let post = ec_dfl post ~qe:qepo ef.ef_po in
  t_equivF_notmod_core post tc

(* -------------------------------------------------------------------- *)
let cond_equivS_notmod ?(mk_other=false) tc cond =
  let env = FApi.tc1_env tc in
  let es = tc1_as_qequivS tc in
  let sl, sr = es.es_sl, es.es_sr in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let modil, modir = s_write env sl, s_write env sr in
  let cond, bdgr, bder = generalize_mod_ env mr modir cond in
  let cond, bdgl, bdel = generalize_mod_ env ml modil cond in
  let cond = f_forall_mems [es.es_ml; es.es_mr] (f_imp es.es_pr.ec_f cond) in
  let bmem = [ml;mr] in
  let bother =
    if mk_other then
      List.flatten [mk_bind_globs env ml bdgl; mk_bind_pvars ml bdel;
                    mk_bind_globs env mr bdgr; mk_bind_pvars mr bder]
    else [] in
  cond, bmem, bother

let t_equivS_notmod_core post tc =
  let es = tc1_as_qequivS tc in
  let _, condp = conseq_eqcond tc es.es_ml es.es_mr es.es_ml es.es_mr es.es_pr es.es_po es.es_pr post in
  let cond1,_,_ = cond_equivS_notmod tc condp in
  let cond2 = f_qequivS_r {es with es_po = post} in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

let t_equivS_notmod post ?qepo tc =
  let es = tc1_as_qequivS tc in
  let post = ec_dfl post ~qe:qepo es.es_po in
  t_equivS_notmod_core post tc

(* -------------------------------------------------------------------- *)
let cond_hoareF_notmod ?(mk_other=false) tc cond =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let hf = tc1_as_hoareF tc in
  let f = hf.hf_f in
  let mpr,mpo = Fun.hoareF_memenv f env in
  let fsig = (Fun.by_xpath f env).f_sig in
  let pvres = pv_res in
  let vres = LDecl.fresh_id hyps "result" in
  let fres = f_local vres fsig.fs_ret in
  let m    = fst mpo in
  let s = PVM.add env pvres m fres PVM.empty in
  let cond = PVM.subst env s cond in
  let modi = f_write env f in
  let cond,bdg,bde = generalize_mod_ env m modi cond in
  let cond = f_forall_simpl [(vres, GTty fsig.fs_ret)] cond in
  assert (fst mpr = m);
  let cond = f_forall_mems [mpr] (f_imp hf.hf_pr cond) in
  let bmem = [m] in
  let bother =
    if mk_other then
      mk_bind_pvar m (vres,()) (pvres, fsig.fs_ret) ::
      List.flatten [mk_bind_globs env m bdg; mk_bind_pvars m bde]
    else [] in
  cond, bmem, bother

let t_hoareF_notmod post tc =
  let hf = tc1_as_hoareF tc in
  let cond1, _, _ = cond_hoareF_notmod tc (f_imp post hf.hf_po) in
  let cond2 = f_hoareF_r { hf with hf_po = post } in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let cond_hoareS_notmod ?(mk_other=false) tc cond =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_hoareS tc in
  let s = hs.hs_s in
  let m = fst hs.hs_m in
  let modi = s_write env s in
  let cond, bdg, bde = generalize_mod_ env m modi cond in
  let cond = f_forall_mems [hs.hs_m] (f_imp hs.hs_pr cond) in
  let bmem = [m] in
  let bother =
    if mk_other then
      List.flatten [mk_bind_globs env m bdg; mk_bind_pvars m bde]
    else [] in
  cond, bmem, bother

let t_hoareS_notmod post tc =
  let hs = tc1_as_hoareS tc in
  let cond1, _, _ = cond_hoareS_notmod tc (f_imp post hs.hs_po) in
  let cond2 = f_hoareS_r {hs with hs_po = post} in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let cond_bdHoareF_notmod ?(mk_other=false) tc cond =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let hf = tc1_as_bdhoareF tc in
  let f = hf.bhf_f in
  let mpr,mpo = Fun.hoareF_memenv f env in
  let fsig = (Fun.by_xpath f env).f_sig in
  let pvres = pv_res in
  let vres = LDecl.fresh_id hyps "result" in
  let fres = f_local vres fsig.fs_ret in
  let m    = fst mpo in
  let s = PVM.add env pvres m fres PVM.empty in
  let cond = PVM.subst env s cond in
  let modi = f_write env f in
  let cond, bdg, bde = generalize_mod_ env m modi cond in
  let cond = f_forall_simpl [(vres, GTty fsig.fs_ret)] cond in
  assert (fst mpr = m);
  let cond = f_forall_mems [mpr] (f_imp hf.bhf_pr cond) in
  let bmem = [m] in
  let bother =
    if mk_other then
      mk_bind_pvar m (vres,()) (pvres, fsig.fs_ret) ::
      List.flatten [mk_bind_globs env m bdg; mk_bind_pvars m bde]
    else [] in
  cond, bmem, bother


let t_bdHoareF_notmod post tc =
  let hf = tc1_as_bdhoareF tc in
  let _, cond =
    bdHoare_conseq_conds hf.bhf_cmp hf.bhf_pr hf.bhf_po hf.bhf_pr post in
  let cond1, _, _ = cond_bdHoareF_notmod tc cond in
  let cond2 = f_bdHoareF_r {hf with bhf_po = post} in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let cond_bdHoareS_notmod ?(mk_other=false) tc cond =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_bdhoareS tc in
  let s = hs.bhs_s in
  let m = fst hs.bhs_m in
  let modi = s_write env s in
  let cond, bdg, bde = generalize_mod_ env m modi cond in
  let cond = f_forall_mems [hs.bhs_m] (f_imp hs.bhs_pr cond) in
  let bmem = [m] in
  let bother =
    if mk_other then
      List.flatten [mk_bind_globs env m bdg; mk_bind_pvars m bde]
    else [] in
  cond, bmem, bother

let t_bdHoareS_notmod post tc =
  let hs = tc1_as_bdhoareS tc in
  let _, cond =
    bdHoare_conseq_conds hs.bhs_cmp hs.bhs_pr hs.bhs_po hs.bhs_pr post in
  let cond1, _, _ = cond_bdHoareS_notmod tc cond in
  let cond2 = f_bdHoareS_r {hs with bhs_po = post} in
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

let gen_qconseq_nm tnm tc pre ?qepr post ?qepo =
  FApi.t_internal ~info:"generic-conseq-nm" (fun g ->
    let gs =
      (tnm post ?qepo @+
        [ t_id;
          tc pre ?qepr post ?qepo @+ [t_id; t_trivial; t_id] ]) g in
    FApi.t_swap_goals 0 1 gs
  )

let t_hoareF_conseq_nm   = gen_conseq_nm t_hoareF_notmod t_hoareF_conseq
let t_hoareS_conseq_nm   = gen_conseq_nm t_hoareS_notmod t_hoareS_conseq

let t_equivF_conseq_nm_core = gen_conseq_nm t_equivF_notmod_core t_equivF_conseq_core
let t_equivS_conseq_nm_core = gen_conseq_nm t_equivS_notmod_core t_equivS_conseq_core

let t_equivF_conseq_nm   = gen_qconseq_nm t_equivF_notmod t_equivF_conseq
let t_equivS_conseq_nm   = gen_qconseq_nm t_equivS_notmod t_equivS_conseq

let t_bdHoareF_conseq_nm = gen_conseq_nm t_bdHoareF_notmod t_bdHoareF_conseq
let t_bdHoareS_conseq_nm = gen_conseq_nm t_bdHoareS_notmod t_bdHoareS_conseq

(* -------------------------------------------------------------------- *)
(* concavity (jenhsen) : E(f g2) <= f (E g2)
   {g1} c { g2} : E g2 <= g1
   increasing :f (E g2) <= f g1
   -----------------------------
   {f g1} c { f g2 }
*)

let t_ehoareF_concave fc pre post tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_ehoareF tc in
  let f = hf.ehf_f in
  let mpr,mpo = Fun.hoareF_memenv f env in
  let fsig = (Fun.by_xpath f env).f_sig in
  let m = fst mpo in
  assert (fst mpr = m && fst mpo = m);
  (* ensure that f only depend of notmod *)
  let modi = f_write env f in
  let modi = PV.add env pv_res fsig.fs_ret modi in
  let fv = PV.fv env m fc in
  let inter = PV.interdep env fv modi in
  if not (PV.is_empty inter) then
    tc_error !!tc "the function should not depend on modified elements: %a"
       (PV.pp env) inter;

  let g0 =
    f_forall_mems [EcMemory.empty_local ~witharg:`None m] (f_concave_incr fc) in

  let g1 =
    let cond = f_xreal_le (f_app_simpl fc [pre] txreal) hf.ehf_pr in
    f_forall_mems [mpr] cond in

  let g2 =
    let cond = f_xreal_le hf.ehf_po (f_app_simpl fc [post] txreal) in
    f_forall_mems [mpo] cond in

  let g3 =
    f_eHoareF pre f post in

  FApi.xmutate1 tc `HlConseq [g0; g1; g2; g3]

(* -------------------------------------------------------------------- *)
let t_ehoareS_concave fc (* xreal -> xreal *) pre post tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_ehoareS tc in
  let s = hs.ehs_s in
  let m = fst hs.ehs_m in
  (* ensure that f only depend of notmod *)
  let modi = s_write env s in
  let fv = PV.fv env m fc in
  let inter = PV.interdep env fv modi in
  if not (PV.is_empty inter) then
    tc_error !!tc "the function should not depend on modified elements: %a"
       (PV.pp env) inter;

  let g0 =
    f_forall_mems [hs.ehs_m] (f_concave_incr fc) in

  let g1 =
    let cond = f_xreal_le (f_app_simpl fc [pre] txreal) hs.ehs_pr in
    f_forall_mems [hs.ehs_m] cond in

  let g2 =
    let cond = f_xreal_le hs.ehs_po (f_app_simpl fc [post] txreal) in
    f_forall_mems [hs.ehs_m] cond in

  let g3 =
    f_eHoareS hs.ehs_m pre s post in

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
  let _mpr,mpo = Fun.hoareF_memenv f env in
  let fsig = (Fun.by_xpath f env).f_sig in
  let _cond1, cond2 = conseq_econd hf.ehf_pr hf.ehf_po pre post in

  let pvres = pv_res in
  let vres = LDecl.fresh_id hyps "result" in
  let fres = f_local vres fsig.fs_ret in
  let m    = fst mpo in
  let s = PVM.add env pvres m fres PVM.empty in
  let cond = PVM.subst env s cond2 in

  let modi = f_write env f in
  let cond,_,_ = generalize_mod_ env m modi cond in
  let cond = f_forall_simpl [(vres, GTty fsig.fs_ret)] cond in

  let fc =
    let x = EcIdent.create "x" in
    f_lambda [x,GTty txreal] (f_interp_ehoare_form cond (f_local x txreal)) in

  (t_ehoareF_concave fc pre post @+ t_ehoare_conseq_nm_end) tc

(* -------------------------------------------------------------------- *)
let t_ehoareS_conseq_nm pre post tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_ehoareS tc in
  let s = hs.ehs_s in
  let m = fst hs.ehs_m in
  let modi = s_write env s in
  let _cond1, cond2 = conseq_econd hs.ehs_pr hs.ehs_po pre post in
  let cond, _bdg, _bde = generalize_mod_ env m modi cond2 in

  let fc =
    let x = EcIdent.create "x" in
    f_lambda [x,GTty txreal] (f_interp_ehoare_form cond (f_local x txreal)) in

  (t_ehoareS_concave fc pre post @+ t_ehoare_conseq_nm_end) tc


(* -------------------------------------------------------------------- *)

let process_concave ((info, fc) : pformula option tuple2 gppterm * pformula) tc =
  let hyps, concl = FApi.tc1_flat tc in

  let fc =
    match concl.f_node with
    | FeHoareS hs ->
      let env = LDecl.push_active hs.ehs_m hyps in
      TTC.pf_process_form !!tc env (tfun txreal txreal) fc

    | FeHoareF hf ->
      let _, env = LDecl.hoareF hf.ehf_f hyps in
      TTC.pf_process_form !!tc env (tfun txreal txreal) fc

    | _ -> tc_error !!tc "conseq concave: not a ehoare judgement"
  in

  let process_cut1 (pre, post) =
    let penv, qenv, gpre, gpost, fmake =
      match concl.f_node with
      | FeHoareS hs ->
        let env = LDecl.push_active hs.ehs_m hyps in
        let fmake pre post = f_eHoareS_r { hs with ehs_pr = pre; ehs_po = post; } in
        (env, env, hs.ehs_pr, hs.ehs_po, fmake)

      | FeHoareF hf ->
        let penv, qenv = LDecl.hoareF hf.ehf_f hyps in
        let fmake pre post =
          f_eHoareF_r { hf with ehf_pr = pre; ehf_po = post } in
        (penv, qenv, hf.ehf_pr, hf.ehf_po, fmake)

      | _ -> tc_error !!tc "conseq concave: not a ehoare judgement"
    in

    let pre   = pre  |> omap (TTC.pf_process_form !!tc penv txreal) |> odfl gpre  in
    let post  = post |> omap (TTC.pf_process_form !!tc qenv txreal) |> odfl gpost in
    fmake pre post

  in

  let f1 = PT.tc1_process_full_closed_pterm_cut
                              ~prcut:(process_cut1) tc info in

  let t_apply_r tc =
    EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true (fst f1) tc in

  match (snd f1).f_node with
  | FeHoareS hs ->
    FApi.t_first t_concave_incr
        (FApi.t_on1seq 3 (t_ehoareS_concave fc hs.ehs_pr hs.ehs_po) t_apply_r tc)

  | FeHoareF hf ->
     FApi.t_first t_concave_incr
       (FApi.t_on1seq 3 (t_ehoareF_concave fc hf.ehf_pr hf.ehf_po) t_apply_r tc)

  | _ -> tc_error !!tc "conseq concave: not a ehoare judgement"






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
let t_bdHoareS_conseq_conj ~add post post' tc =
  let hs = tc1_as_bdhoareS tc in
  let postc = if add then f_and post' post else post' in
  let posth = if add then post' else f_and post' post in
  if not (f_equal hs.bhs_po postc) then
    tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareS hs.bhs_m hs.bhs_pr hs.bhs_s post in
  let concl2 = f_bdHoareS_r { hs with bhs_po = posth } in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)
let t_bdHoareF_conseq_conj ~add post post' tc =
  let hs = tc1_as_bdhoareF tc in
  let postc = if add then f_and post' post else post' in
  let posth = if add then post' else f_and post' post in
  if not (f_equal hs.bhf_po postc) then
    tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareF hs.bhf_pr hs.bhf_f post in
  let concl2 = f_bdHoareF_r { hs with bhf_po = posth } in
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
    match side with
    | `Left  -> es.es_ml, es.es_sl, es.es_sr
    | `Right -> es.es_mr, es.es_sr, es.es_sl
  in
  if not (List.is_empty s'.s_node) then begin
    let side = side2str (negside side) in
    tc_error !!tc "%s statement should be empty" side
  end;
  let subst = Fsubst.f_subst_mem mhr (fst m) in
  let prs, pos = subst pr, subst po in
  if not (f_equal prs es.es_pr && f_equal pos es.es_po) then
    tc_error !!tc "invalid pre- or post-condition";
  let g1 = f_bdHoareS (mhr,snd m) pr s po FHeq f_r1 in
  FApi.xmutate1 tc `HlBdEquiv [g1]

(* -------------------------------------------------------------------- *)

(*
(forall m1, P1 m1 => exists m2, P m1 m2 /\ P2 m2)
(forall m1 m2, Q m1 m2 => Q2 m2 => Q1 m1)
equiv M1 ~ M2 : P ==> Q   hoare M2 : P2 ==> Q2.
-----------------------------------------------
hoare M1 : P1 ==> Q1.
*)

let transitivity_side_cond hyps prml poml pomr p q p2 q2 p1 q1 =
  let env = LDecl.toenv hyps in
  let cond1 =
    let fv1 = PV.fv env mright p in
    let fv2 = PV.fv env mhr p2 in
    let fv = PV.union fv1 fv2 in
    let elts, glob = PV.ntr_elements fv in
    let bd, s = generalize_subst env mhr elts glob in
    let s1 = PVM.of_mpv s mright in
    let s2 = PVM.of_mpv s mhr in
    let concl = f_and (PVM.subst env s1 p) (PVM.subst env s2 p2) in
    let p1 = Fsubst.f_subst_mem mhr mleft p1 in
    f_forall_mems [prml] (f_imp p1 (f_exists bd concl)) in
  let cond2 =
    let q1 = Fsubst.f_subst_mem mhr mleft q1 in
    let q2 = Fsubst.f_subst_mem mhr mright q2 in
    f_forall_mems [poml; pomr] (f_imps [q;q2] q1) in
  (cond1, cond2)

let t_hoareF_conseq_equiv f2 p q p2 q2 tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let hf1 = tc1_as_hoareF tc in
  let ef  = f_equivF p hf1.hf_f f2 q in
  let hf2 = f_hoareF p2 f2 q2 in
  let (prml, _prmr), (poml, pomr) = Fun.equivF_memenv hf1.hf_f f2 env in
  let (cond1, cond2) =
    transitivity_side_cond hyps prml poml pomr p q p2 q2 hf1.hf_pr hf1.hf_po in
  FApi.xmutate1 tc `HoareFConseqEquiv [cond1; cond2; ef; hf2]

let t_bdHoareF_conseq_equiv f2 p q p2 q2 tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let hf1 = tc1_as_bdhoareF tc in
  let ef  = f_equivF p hf1.bhf_f f2 q in
  let hf2 = f_bdHoareF p2 f2 q2 hf1.bhf_cmp hf1.bhf_bd in
  let (prml, _prmr), (poml, pomr) = Fun.equivF_memenv hf1.bhf_f f2 env in
  let (cond1, cond2) =
    transitivity_side_cond hyps prml poml pomr p q p2 q2 hf1.bhf_pr hf1.bhf_po in
  FApi.xmutate1 tc `BdHoareFConseqEquiv [cond1; cond2; ef; hf2]


let t_ehoareF_conseq_equiv f2 p q p2 q2 tc =
  let env = FApi.tc1_env tc in
  let hf1 = tc1_as_ehoareF tc in
  let ef  = f_equivF p hf1.ehf_f f2 q in
  let hf2 = f_eHoareF p2 f2 q2 in
  let (prml, _prmr), (poml, pomr) = Fun.equivF_memenv hf1.ehf_f f2 env in
  let p1 = hf1.ehf_pr and q1 = hf1.ehf_po in
  let cond1 =
    let fv1 = PV.fv env mright p in
    let fv2 = PV.fv env mhr p2 in
    let fv = PV.union fv1 fv2 in
    let elts, glob = PV.ntr_elements fv in
    let bd, s = generalize_subst env mhr elts glob in
    let s1 = PVM.of_mpv s mright in
    let s2 = PVM.of_mpv s mhr in
    let p1 = Fsubst.f_subst_mem mhr mleft p1 in
    let concl =
     f_or (f_eq p1 f_xreal_inf)
       (f_and (PVM.subst env s1 p) (f_xreal_le (PVM.subst env s2 p2) p1)) in
    f_forall_mems [prml] (f_exists bd concl) in
  let cond2 =
    let q1 = Fsubst.f_subst_mem mhr mleft q1 in
    let q2 = Fsubst.f_subst_mem mhr mright q2 in
    f_forall_mems [poml; pomr] (f_imp q (f_xreal_le q1 q2)) in
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
    t_on1 2 (t_apply_r nf1) (tac hs.hs_pr hs.hs_po tc)

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
      (tac (f_and hs.hs_pr hs2.hs_pr) (f_and hs.hs_po hs2.hs_po))
      (FApi.t_seqsub
         (t_hoareS_conseq_conj hs2.hs_pr hs2.hs_po hs.hs_pr hs.hs_po)
         [t_apply_r nf2; t_apply_r nf1])
      tc

  (* ------------------------------------------------------------------ *)
  (* hoareS / bdhoareS / ⊥ / ⊥                                          *)
  | FhoareS _, Some ((_, {f_node = FbdHoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in

    check_is_detbound `First hs.bhs_bd;

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

    check_is_detbound `First hs.bhf_bd;

    FApi.t_seq
      t_hoareF_conseq_bdhoare
      (t_on1seq 1
         (t_bdHoareF_conseq_bd hs.bhf_cmp hs.bhf_bd)
         (t_on1seq 2 (tac hs.bhf_pr hs.bhf_po) (t_apply_r nf1)))
      tc
  (* ------------------------------------------------------------------ *)
  (* hoareF / equivF / hoareF                                           *)
  | FhoareF _,
    Some ((_, {f_node = FequivF ef}) as nef), Some((_, f2) as nf2), _ ->
    let hf2 = pf_as_hoareF !!tc f2 in
    let ef = equivF ef in
    FApi.t_seqsub
      (t_hoareF_conseq_equiv hf2.hf_f ef.ef_pr ef.ef_po hf2.hf_pr hf2.hf_po)
      [t_id; t_id; t_apply_r nef; t_apply_r nf2] tc

  (* ------------------------------------------------------------------ *)
  (* ehoareS / ehoareS / ⊥ / ⊥                                            *)
  | FeHoareS _, Some ((_, {f_node = FeHoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_ehoareS_conseq_nm else t_ehoareS_conseq in
    FApi.t_last (t_apply_r nf1) (tac hs.ehs_pr hs.ehs_po tc)

  (* ------------------------------------------------------------------ *)
  (* ehoareF / ehoareF / ⊥ / ⊥                                            *)
  | FeHoareF _, Some ((_, {f_node = FeHoareF hf}) as nf1), None, None ->
    let tac = if notmod then t_ehoareF_conseq_nm else t_ehoareF_conseq in
    FApi.t_last (t_apply_r nf1) (tac hf.ehf_pr hf.ehf_po tc)

  (* ------------------------------------------------------------------ *)
  (* ehoareF / equivF / ehoareF                                           *)
  | FeHoareF _,
    Some ((_, {f_node = FequivF ef}) as nef), Some((_, f2) as nf2), _ ->
    let ef = equivF ef in
    let hf2 = pf_as_ehoareF !!tc f2 in
    FApi.t_seqsub
      (t_ehoareF_conseq_equiv hf2.ehf_f ef.ef_pr ef.ef_po hf2.ehf_pr hf2.ehf_po)
      [t_id; t_id; t_apply_r nef; t_apply_r nf2] tc

  (* ------------------------------------------------------------------ *)
  (* bdhoareS / bdhoareS / ⊥ / ⊥                                        *)
  | FbdHoareS _, Some ((_, {f_node = FbdHoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in

    t_on1seq 1
      (t_bdHoareS_conseq_bd hs.bhs_cmp hs.bhs_bd)
      (t_on1seq 2 (tac hs.bhs_pr hs.bhs_po) (t_apply_r nf1))
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
    let pre    = f_and hs.bhs_pr hs2.hs_pr in
    let mpre   = Fsubst.f_subst_mem mhr m pre in
    let post1  = hs0.bhs_po in
    let post   = hs.bhs_po in
    let posta  = f_and post hs2.hs_po in

    let concl1 = f_forall_mems [hs0.bhs_m] (f_imp hs0.bhs_pr pre) in

    let tc = ( t_cut concl1 @+
        [ t_id;   (* subgoal 1 : pre *)
          t_intro_i hi @!
          t_cut (f_hoareS_r {hs2 with hs_pr = pre}) @+ [
            t_hoareS_conseq hs2.hs_pr hs2.hs_po @+
                [ EcLowGoal.t_trivial;
                  t_mytrivial;
                  t_clear hi (* subgoal 2 : hs2 *)];
            t_intro_i hh @!
            (t_bdHoareS_conseq_bd hs.bhs_cmp hs.bhs_bd @+ [
              t_id; (* subgoal 3 : bound *)
              t_bdHoareS_conseq_conj ~add:false hs2.hs_po post1 @+ [
                t_hoareS_conseq pre hs2.hs_po @+ [
                  t_intros_i [m;h0] @! t_cutdef
                    (ptlocal ~args:[pamemory m; palocal h0] hi)
                    mpre @! EcLowGoal.t_trivial;
                  t_mytrivial;
                  t_apply_hyp hh];
                tac pre posta @+ [
                  t_apply_hyp hi;
                  t_id; (* subgoal 4 : post *)
                  t_bdHoareS_conseq_conj ~add:true hs2.hs_po post @+ [
                    t_apply_hyp hh;
                    t_bdHoareS_conseq hs.bhs_pr post @+ [
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
      (t_bdHoareF_conseq_bd hs.bhf_cmp hs.bhf_bd)
      (t_on1seq 2 (tac hs.bhf_pr hs.bhf_po) (t_apply_r nf1))
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
    let pre    = f_and hs.bhf_pr hs2.hf_pr in
    let mpre   = Fsubst.f_subst_mem mhr m pre in
    let post1  = hs0.bhf_po in
    let post   = hs.bhf_po in
    let posta  = f_and post hs2.hf_po in
    let mpr,_ = EcEnv.Fun.hoareF_memenv hs0.bhf_f (FApi.tc1_env tc) in
    let concl1 = f_forall_mems [mpr] (f_imp hs0.bhf_pr pre) in

    let tc = ( t_cut concl1 @+
        [ t_id;   (* subgoal 1 : pre *)
          t_intro_i hi @!
          t_cut (f_hoareF_r {hs2 with hf_pr = pre}) @+ [
            t_hoareF_conseq hs2.hf_pr hs2.hf_po @+
                [ EcLowGoal.t_trivial;
                  t_mytrivial;
                  t_clear hi (* subgoal 2 : hs2 *)];
            t_intro_i hh @!
            (t_bdHoareF_conseq_bd hs.bhf_cmp hs.bhf_bd @+ [
              t_id; (* subgoal 3 : bound *)
              t_bdHoareF_conseq_conj ~add:false hs2.hf_po post1 @+ [
                t_hoareF_conseq pre hs2.hf_po @+ [
                  t_intros_i [m;h0] @! t_cutdef
                    (ptlocal ~args:[pamemory m; palocal h0] hi)
                    mpre @! EcLowGoal.t_trivial;
                  t_mytrivial;
                  t_apply_hyp hh];
                tac pre posta @+ [
                  t_apply_hyp hi;
                  t_id; (* subgoal 4 : post *)
                  t_bdHoareF_conseq_conj ~add:true hs2.hf_po post @+ [
                    t_apply_hyp hh;
                    t_bdHoareF_conseq hs.bhf_pr post @+ [
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
  (* bdhoareF / equivF / bdhoareF                                           *)
  | FbdHoareF _,
    Some ((_, {f_node = FequivF ef}) as nef), Some((_, f2) as nf2), _ ->
    let hf2 = pf_as_bdhoareF !!tc f2 in
    let ef = equivF ef in
    FApi.t_seqsub
      (t_bdHoareF_conseq_equiv hf2.bhf_f ef.ef_pr ef.ef_po hf2.bhf_pr hf2.bhf_po)
      [t_id; t_id; t_apply_r nef; t_apply_r nf2] tc

  (* ------------------------------------------------------------------ *)
  (* equivS / equivS / ⊥ / ⊥                                            *)
  | FequivS _, Some ((_, {f_node = FequivS es}) as nf1), None, None ->
    let tac = if notmod then t_equivS_conseq_nm_core else
                (t_equivS_conseq_core ~witheq:true) in
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
    let es = equivS es in
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
    let es = equivS es in
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
    let es = equivS es in
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

    check_is_detbound `Second hs.bhs_bd;

    t_on1seq 2
     (tac pre post)
     (FApi.t_seq
        (t_equivS_conseq_bd `Left hs.bhs_pr hs.bhs_po)
        (t_apply_r nf2))
     tc

  (* ------------------------------------------------------------------ *)
  (* equivS / ⊥ / ⊥ / bdhoareS                                          *)
  | FequivS _, None, None, Some ((_, f3) as nf3) ->
    let subst2 = Fsubst.f_subst_mem mhr mright in
    let hs = pf_as_bdhoareS !!tc f3 in
    let pre, post = subst2 hs.bhs_pr, subst2 hs.bhs_po in
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    check_is_detbound `Third hs.bhs_bd;

    t_on1seq 2
      (tac pre post)
      (FApi.t_seq
         (t_equivS_conseq_bd `Right hs.bhs_pr hs.bhs_po)
         (t_apply_r nf3))
      tc

  (* ------------------------------------------------------------------ *)
  (* equivF / equivF / ⊥ / ⊥                                            *)
  | FequivF _, Some ((_, {f_node = FequivF ef}) as nf1), None, None ->
    let tac = if notmod then t_equivF_conseq_nm_core else t_equivF_conseq_core in
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
    let ef = equivF ef in
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
type processed_conseq_info =
  | PCI_bd of hoarecmp option * form

let process_info pe hyps = function
  | CQI_bd (cmp, bd) -> PCI_bd (cmp, TTC.pf_process_form pe hyps treal bd)

let process_conseq notmod ((info1, info2, info3) : conseq_ppterm option tuple3) tc =
  let hyps, concl = FApi.tc1_flat tc in

  let ensure_none o =
    if not (is_none o) then tc_error !!tc "cannot give a bound here" in

  let ensure_no_qe (f, qe) =
    if is_none qe then f
    else tc_error !!tc "cannot give a quantum equality here" in

  let process_conseq_pec pe hyps ty (d_f,d_ec) (f,ec) =
    let f = f |> omap (TTC.pf_process_form pe hyps ty) |> odfl d_f in
    let ec =
      match d_ec with
      | None ->
          let check pqe =
            tc_error ~loc:(EcLocation.lmergeall pqe) !!tc "cannot give a quantum equality here" in
          omap check ec
      | Some (ml,mr,d_ec) ->
        assert (ty_equal ty tbool);
        Some (ec |> omap (TTC.pf_process_qe pe hyps ml mr) |> odfl d_ec) in
    (f, ec) in

  let ec_some ml mr ec = ec.ec_f, Some (ml, mr, ec.ec_e) in
  let some_ec (f, oqe) = { ec_f = f; ec_e = oget oqe } in

  let process_cut1 ((pre, post), bd) =
     let penv, qenv, gpre, gpost, ty, fmake =
      match concl.f_node with
      | FhoareS hs ->
        let env = LDecl.push_active hs.hs_m hyps in

        let fmake pre post c_or_bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          match c_or_bd with
          | None ->
            f_hoareS_r { hs with hs_pr = pre; hs_po = post; }
          | Some (PCI_bd (cmp, bd)) ->
            f_bdHoareS hs.hs_m pre hs.hs_s post (oget cmp) bd
        in (env, env, (hs.hs_pr, None), (hs.hs_po, None), tbool, fmake)

      | FhoareF hf ->
        let penv, qenv = LDecl.hoareF hf.hf_f hyps in

        let fmake pre post c_or_bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          match c_or_bd with
          | None ->
            f_hoareF pre hf.hf_f post
          | Some (PCI_bd (cmp, bd)) ->
            f_bdHoareF pre hf.hf_f post (oget cmp) bd

        in (penv, qenv, (hf.hf_pr,None), (hf.hf_po,None), tbool, fmake)

      | FeHoareS hs ->
        let env = LDecl.push_active hs.ehs_m hyps in
        let fmake pre post bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          ensure_none bd;
          f_eHoareS_r { hs with ehs_pr = pre; ehs_po = post; } in
        (env, env, (hs.ehs_pr, None), (hs.ehs_po, None), txreal, fmake)

      | FeHoareF hf ->
        let penv, qenv = LDecl.hoareF hf.ehf_f hyps in
        let fmake pre post bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          ensure_none bd;
          f_eHoareF_r { hf with ehf_pr = pre; ehf_po = post } in
        (penv, qenv, (hf.ehf_pr, None), (hf.ehf_po, None), txreal, fmake)

      | FbdHoareS bhs ->
        let env = LDecl.push_active bhs.bhs_m hyps in

        let fmake pre post c_or_bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          match c_or_bd with
          | None                   ->
            f_bdHoareS_r { bhs with bhs_pr = pre;
                                    bhs_po = post; }
          | Some (PCI_bd (cmp,bd)) ->
            let cmp = odfl bhs.bhs_cmp cmp in
            f_bdHoareS_r { bhs with bhs_pr = pre;
                                    bhs_po = post;
                                    bhs_cmp = cmp;
                                    bhs_bd = bd; }
        in

        (env, env, (bhs.bhs_pr,None), (bhs.bhs_po,None), tbool, fmake)

      | FbdHoareF hf ->
        let penv, qenv = LDecl.hoareF hf.bhf_f hyps in

        let fmake pre post c_or_bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          match c_or_bd with
          | None                   ->
            f_bdHoareF pre hf.bhf_f post hf.bhf_cmp hf.bhf_bd
          | Some (PCI_bd (cmp,bd)) ->
            let cmp = odfl hf.bhf_cmp cmp in
            f_bdHoareF pre hf.bhf_f post cmp bd
        in

        (penv, qenv, (hf.bhf_pr,None), (hf.bhf_po,None), tbool, fmake)

      | FequivF ef ->
        let penv, qenv = LDecl.equivF ef.ef_fl ef.ef_fr hyps in
        let fmake pre post c_or_bd =
          ensure_none c_or_bd;
          f_qequivF (some_ec pre) ef.ef_fl ef.ef_fr (some_ec post)
        in
        let ec_some = ec_some mleft mright in
        (penv, qenv, ec_some ef.ef_pr, ec_some ef.ef_po, tbool, fmake)

      | FequivS es ->
        let env = LDecl.push_all [es.es_ml; es.es_mr] hyps in
        let fmake pre post c_or_bd =
          ensure_none c_or_bd;
          f_qequivS_r { es with es_pr = some_ec pre; es_po = some_ec post; }
        in
        let ec_some = ec_some (fst es.es_ml) (fst es.es_mr) in
        (env, env, ec_some es.es_pr, ec_some es.es_po, tbool, fmake)

      | _ -> tc_error !!tc "conseq: not a phl/prhl judgement"
    in

    let pre   = process_conseq_pec !!tc penv ty gpre pre in
    let post  = process_conseq_pec !!tc qenv ty gpost post in
    let bd = bd |> omap (process_info !!tc penv) in

    fmake pre post bd

  in

  let process_cut2 side f1 ((pre, post), bd) =
    let penv, qenv, gpre, gpost, ty, fmake =
      match concl.f_node with
      | FhoareS hs ->
        let env = LDecl.push_active hs.hs_m hyps in
        let fmake pre post bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          ensure_none bd;
          f_hoareS_r { hs with hs_pr = pre; hs_po = post; }
        in (env, env, (hs.hs_pr, None), (hs.hs_po, None), tbool, fmake)

      | FhoareF hf ->
        let f, pr, po = match f1 with
        | None -> hf.hf_f, hf.hf_pr, hf.hf_po
        | Some f1 -> match (snd f1).f_node with
                     | FequivF ef when side = `Left -> ef.ef_fr, f_true, f_true
                     | _ -> hf.hf_f, hf.hf_pr, hf.hf_po
        in
        let penv, qenv = LDecl.hoareF f hyps in
        let fmake pre post bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          ensure_none bd; f_hoareF pre f post in
        (penv, qenv, (pr,None), (po,None), tbool, fmake)

      | FeHoareF hf ->
        let f, pr, po = match f1 with
        | None -> hf.ehf_f, hf.ehf_pr, hf.ehf_po
        | Some f1 -> match (snd f1).f_node with
                     | FequivF ef when side = `Left ->
                         let f_xreal_1 = f_r2xr f_r1 in
                         ef.ef_fr, f_xreal_1, f_xreal_1
                     | _ -> hf.ehf_f, hf.ehf_pr, hf.ehf_po
        in
        let penv, qenv = LDecl.hoareF f hyps in
        let fmake pre post bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          ensure_none bd; f_eHoareF pre f post in
        (penv, qenv, (pr, None), (po, None), txreal, fmake)

      | FbdHoareS bhs ->
        let env = LDecl.push_active bhs.bhs_m hyps in
        let fmake pre post bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          ensure_none bd;
          f_hoareS bhs.bhs_m pre bhs.bhs_s post
        in (env, env, (bhs.bhs_pr, None), (bhs.bhs_po,None), tbool, fmake)

      | FbdHoareF bhf ->
        let f, pr, po = match f1 with
        | None -> bhf.bhf_f, bhf.bhf_pr, bhf.bhf_po
        | Some f1 -> match (snd f1).f_node with
                     | FequivF ef when side = `Left -> ef.ef_fr, f_true, f_true
                     | _ -> bhf.bhf_f, bhf.bhf_pr, bhf.bhf_po
        in
        let penv, qenv = LDecl.hoareF f hyps in
        let fmake pre post bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          ensure_none bd; f_hoareF pre f post in
        (penv, qenv, (pr,None), (po,None), tbool, fmake)

      | FequivF ef ->
        let f = sideif side ef.ef_fl ef.ef_fr in
        let penv, qenv = LDecl.hoareF f hyps in
        let fmake pre post bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          ensure_none bd;
          f_hoareF pre f post in
        (penv, qenv, (f_true,None), (f_true,None), tbool, fmake)

      | FequivS es ->
        let f = sideif side es.es_sl es.es_sr in
        let m = sideif side es.es_ml es.es_mr in
        let m = (mhr, snd m) in
        let env = LDecl.push_active m hyps in
        let fmake pre post bd =
          let pre, post = ensure_no_qe pre, ensure_no_qe post in
          match info1, bd with
          | None, Some (PCI_bd (cmp,bd)) ->
            let cmp = odfl FHeq cmp in
            f_bdHoareS m pre f post cmp bd

          | None, None ->
            let cmp, bd = FHeq, f_r1 in
            f_bdHoareS m pre f post cmp bd

          | _, None ->
            f_hoareS m pre f post

          | _, Some (PCI_bd (cmp,bd)) ->
            let cmp = odfl FHeq cmp in
            f_bdHoareS m pre f post cmp bd


        in (env, env, (f_true,None), (f_true,None), tbool, fmake)

      | _ -> tc_error !!tc "conseq: not a phl/prhl judgement"
    in

    let pre   = process_conseq_pec !!tc penv ty gpre pre in
    let post  = process_conseq_pec !!tc qenv ty gpost post in
    let bd    = bd |> omap (process_info !!tc penv) in

    fmake pre post bd

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
  let info = FPCut (((Some pr,None), (Some po,None)), None) in
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
    | FhoareF hf  -> Some (t_hoareF_notmod, cond_hoareF_notmod ~mk_other tc hf.hf_po)
    | FhoareS hs  -> Some (t_hoareS_notmod, cond_hoareS_notmod ~mk_other tc hs.hs_po )
    | FbdHoareF hf -> Some (t_bdHoareF_notmod, cond_bdHoareF_notmod ~mk_other tc hf.bhf_po)
    | FbdHoareS hs -> Some (t_bdHoareS_notmod, cond_bdHoareS_notmod ~mk_other tc hs.bhs_po)
    | FequivF ef   ->
        let ef = equivF ef in
        Some (t_equivF_notmod ?qepo:None, cond_equivF_notmod ~mk_other tc ef.ef_po)
    | FequivS es   ->
        let es = equivS es in
        Some (t_equivS_notmod ?qepo:None, cond_equivS_notmod ~mk_other tc es.es_po )
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
        let s = List.fold_left2 Fsubst.f_bind_local s other (List.map snd bdo) in
        Fsubst.f_subst s concl in

    let t_end = FApi.t_try (t_crush ~delta ?tsolve @! t_fail) in
    FApi.t_first t_end (t_notmod post tc)
