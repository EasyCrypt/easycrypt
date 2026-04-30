(* -------------------------------------------------------------------- *)
(* Consequence tactics for all EasyCrypt program logics.                  *)
(*                                                                       *)
(* This module implements the "conseq" family of tactics, which allow     *)
(* strengthening preconditions and weakening postconditions of program    *)
(* logic judgments. It covers all logic flavors:                          *)
(*   - hoare   (Hoare logic, F/S)                                        *)
(*   - bdhoare (bounded Hoare logic, F/S)                                *)
(*   - ehoare  (expected-value Hoare logic, F/S)                         *)
(*   - equiv   (relational/equivalence logic, F/S)                       *)
(*   - eager   (eager equivalence logic, F only)                         *)
(*                                                                       *)
(* Naming convention for tactics:                                        *)
(*   t_<logic><level>_<variant>                                          *)
(* where:                                                                *)
(*   logic   = hoare | bdHoare | ehoare | equiv | eager                  *)
(*   level   = F (function-level) | S (statement-level)                  *)
(*   variant = conseq      — basic consequence rule                      *)
(*           | conseq_nm   — consequence with non-modification framing   *)
(*           | conseq_bd   — consequence with bound change (bdhoare)     *)
(*           | conseq_conj — consequence via conjunction                 *)
(*           | conseq_equiv— consequence via equivalence (transitivity)  *)
(*           | notmod      — non-modification postcondition weakening    *)
(*           | concave     — concavity/Jensen rule (ehoare)              *)
(*                                                                       *)
(* Processing pipeline (user tactic → logical rule):                     *)
(*   process_conseq_opt                                                  *)
(*     → process_conseq                                                  *)
(*       → process_conseq_hs (hoare with exception postconditions)       *)
(*       | process_conseq_ss (all other judgment types)                  *)
(*         → process_conseq_core (shared proof-term processing)          *)
(*           → t_hi_conseq (high-level dispatcher)                       *)
(*             → t_hi_conseq_<goal_type> (per-goal-type logic)           *)
(*               → t_<logic><level>_<variant> (core logical rules)       *)
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
(* Condition builders for consequence rules.                             *)
(*                                                                       *)
(* These helpers build the side conditions (implications) that arise      *)
(* from applying the consequence rule:                                   *)
(*   {sP} c {sQ}   P ⇒ sP   sQ ⇒ Q                                    *)
(*   ————————————————————————————————                                    *)
(*              {P} c {Q}                                                *)
(* -------------------------------------------------------------------- *)
let conseq_cond_ss
    (pre   : ss_inv)
    (post  : ss_inv)
    (spre  : ss_inv)
    (spost : ss_inv)
=
  map_ss_inv2 f_imp pre spre, map_ss_inv2 f_imp spost post

let conseq_cond_ts
    (pre   : ts_inv)
    (post  : ts_inv)
    (spre  : ts_inv)
    (spost : ts_inv)
=
  map_ts_inv2 f_imp pre spre, map_ts_inv2 f_imp spost post

(*
{ sF } c { sf }  sF <= F  f <= sf
--------------------------------------------------------------------
{ F } c { f }
 *)
let conseq_econd
    (pre   : ss_inv)
    (post  : ss_inv)
    (spre  : ss_inv)
    (spost : ss_inv)
=
  let spre = ss_inv_rebind spre pre.m in
  let spost = ss_inv_rebind spost post.m in
  map_ss_inv2 f_xreal_le spre pre, map_ss_inv2 f_xreal_le post spost

let bd_goal_r (fcmp : hoarecmp) (fbd : ss_inv) (cmp : hoarecmp) (bd : ss_inv) =
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

let bd_goal
    (tc   : tcenv1)
    (fcmp : hoarecmp)
    (fbd  : ss_inv)
    (cmp  : hoarecmp)
    (bd   : ss_inv)
=
  match bd_goal_r fcmp fbd cmp bd with
  | None    ->
    let ppe = EcPrinting.PPEnv.ofenv (FApi.tc1_env tc) in
    tc_error !!tc
      "do not know how to change phoare[...]%s %a into phoare[...]%s %a"
      (EcPrinting.string_of_hcmp fcmp) (EcPrinting.pp_form ppe) fbd.inv
      (EcPrinting.string_of_hcmp cmp) (EcPrinting.pp_form ppe) bd.inv
  | Some fp -> fp

(* -------------------------------------------------------------------- *)
(* Core consequence tactics (one per logic × level).                     *)
(*                                                                       *)
(* Each t_<logic><level>_conseq implements the basic consequence rule:   *)
(* given new pre/postconditions, generate subgoals for the implications  *)
(* and the judgment with the new conditions.                             *)
(* -------------------------------------------------------------------- *)

(* hoareF consequence rule:
 *
 *   ∀m, P m ⇒ P' m    ∀m, Q' m ⇒ Q m [∧ Qe]    hoare[f] P' ==> Q'[/Qe]
 *   ———————————————————————————————————————————————————————————————————————
 *                         hoare[f] P ==> Q[/Qe₀]
 *
 * where Q[/Qe₀] denotes the main postcondition Q with exception map Qe₀,
 * and Qe are the merged exception postcondition obligations. *)
let t_hoareF_conseq (pre : ss_inv) (post : hs_inv) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hf  = tc1_as_hoareF tc in
  let pre = ss_inv_rebind pre hf.hf_m in
  let post = hs_inv_rebind post hf.hf_m in
  let post, epost = POE.destruct post.hsi_inv in
  let fpost, fepost = POE.destruct (hf_po hf).hsi_inv in
  let mpr,mpo = EcEnv.Fun.hoareF_memenv hf.hf_m hf.hf_f env in
  let m = hf.hf_m in
  let cond1, cond2 =
    conseq_cond_ss (hf_pr hf) {m;inv=fpost} pre {m;inv=post}
  in
  let cond2e = TTC.merge2_poe_list fepost epost in
  let cond2 = List.fold f_and cond2.inv cond2e in
  let concl1 = f_forall_mems_ss_inv mpr cond1 in
  let concl2 = f_forall_mems_ss_inv mpo {m;inv=cond2} in
  let concl3 = f_hoareF pre hf.hf_f { hsi_m = m; hsi_inv = POE.mk post epost} in
  FApi.xmutate1 tc `Conseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)

(* hoareS consequence rule: same as hoareF but for statements. *)
let t_hoareS_conseq (pre : ss_inv) (post : hs_inv) (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let pre = ss_inv_rebind pre (fst hs.hs_m) in
  let post = hs_inv_rebind post (fst hs.hs_m) in
  let post, epost = POE.destruct post.hsi_inv in
  let fpost, fepost = POE.destruct (hs_po hs).hsi_inv in
  let m = fst hs.hs_m in
  let cond1, cond2 =
    conseq_cond_ss (hs_pr hs) {m;inv=fpost} pre {m;inv=post}
  in
  let cond2e = TTC.merge2_poe_list fepost epost in
  let cond2 = List.fold f_and cond2.inv cond2e in
  let concl1 = f_forall_mems_ss_inv hs.hs_m cond1 in
  let concl2 = f_forall_mems_ss_inv hs.hs_m {m=fst hs.hs_m;inv=cond2} in
  let concl3 =
    f_hoareS (snd hs.hs_m) pre hs.hs_s { hsi_m = m; hsi_inv = POE.mk post epost }
  in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)

(* ehoareF consequence rule (expected Hoare logic):
 *
 *   ∀m, P' m ≤ P m    ∀m, Q m ≤ Q' m    ehoare[f] P' ==> Q'
 *   ——————————————————————————————————————————————————————————
 *                    ehoare[f] P ==> Q
 *
 * Note: xreal_le (<=) is the ehoare analogue of implication (=>). *)
let t_ehoareF_conseq (pre : ss_inv) (post : ss_inv) (tc : tcenv1) =
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

(* ehoareS consequence rule: same as ehoareF but for statements. *)
let t_ehoareS_conseq (pre : ss_inv) (post : ss_inv) (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  let cond1, cond2 =
    conseq_econd (ehs_pr hs) (ehs_po hs) pre post in
  let concl1 = f_forall_mems_ss_inv hs.ehs_m cond1 in
  let concl2 = f_forall_mems_ss_inv hs.ehs_m cond2 in
  let concl3 = f_eHoareS (snd hs.ehs_m) pre hs.ehs_s post in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)

(* Build side conditions for bdHoare consequence.
 * The postcondition condition depends on the comparison operator:
 *   FHle: Q ⇒ Q'  (weaken)    FHeq: Q ⇔ Q'  (equiv)    FHge: Q' ⇒ Q *)
let bdHoare_conseq_conds
    (cmp    : hoarecmp)
    (pr     : ss_inv)
    (po     : ss_inv)
    (new_pr : ss_inv)
    (new_po : ss_inv)
=
  let cond1, cond2 = conseq_cond_ss pr po new_pr new_po in
  let cond2 = match cmp with
    | FHle -> map_ss_inv2 f_imp po new_po
    | FHeq -> map_ss_inv2 f_iff po new_po
    | FHge -> cond2
  in
  cond1, cond2

(* -------------------------------------------------------------------- *)

(* bdHoareF consequence rule:
 *
 *   ∀m, P m ⇒ P' m    ∀m, Q' m ⇒/⇔/⇐ Q m    phoare[f] P' ==> Q' cmp bd
 *   —————————————————————————————————————————————————————————————————————
 *                     phoare[f] P ==> Q cmp bd
 *
 * The postcondition direction depends on cmp:
 *   FHle (≤): Q' ⇒ Q    FHeq (=): Q' ⇔ Q    FHge (≥): Q ⇒ Q' *)
let t_bdHoareF_conseq (pre : ss_inv) (post : ss_inv) (tc : tcenv1) =
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

(* bdHoareS consequence rule: same as bdHoareF but for statements. *)
let t_bdHoareS_conseq (pre : ss_inv) (post : ss_inv) (tc : tcenv1) =
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

(* bdHoareF bound change rule:
 *
 *   ∀m, P m ⇒ (bd' cmp' bd)    phoare[f] P ==> Q cmp' bd'
 *   ————————————————————————————————————————————————————————
 *              phoare[f] P ==> Q cmp bd
 *
 * Changes the bound and/or comparison operator. *)
let t_bdHoareF_conseq_bd (cmp : hoarecmp) (bd : ss_inv) (tc : tcenv1) =
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

(* bdHoareS bound change rule: same as bdHoareF_conseq_bd for statements. *)
let t_bdHoareS_conseq_bd (cmp : hoarecmp) (bd : ss_inv) (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  let bd = ss_inv_rebind bd (fst bhs.bhs_m) in
  let bd_goal = bd_goal tc bhs.bhs_cmp (bhs_bd bhs) cmp bd in
  let concl = f_bdHoareS (snd bhs.bhs_m) (bhs_pr bhs) bhs.bhs_s (bhs_po bhs) cmp bd in
  let imp = map_ss_inv2 f_imp (bhs_pr bhs) bd_goal in
  let bd_goal = f_forall_mems_ss_inv bhs.bhs_m imp in
  FApi.xmutate1 tc `HlConseq [bd_goal; concl]

(* -------------------------------------------------------------------- *)

(* equivF consequence rule:
 *
 *   ∀ml mr, P ml mr ⇒ P' ml mr    ∀ml mr, Q' ml mr ⇒ Q ml mr
 *   equiv[f1 ~ f2] P' ==> Q'
 *   ————————————————————————————————————————————————————————————
 *              equiv[f1 ~ f2] P ==> Q                           *)
let t_equivF_conseq (pre : ts_inv) (post : ts_inv) (tc : tcenv1) =
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

(* eagerF consequence rule: same as equivF but for eager judgments. *)
let t_eagerF_conseq (pre : ts_inv) (post : ts_inv) (tc : tcenv1) =
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

(* equivS consequence rule: same as equivF but for statements. *)
let t_equivS_conseq (pre : ts_inv) (post : ts_inv) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let pre = ts_inv_rebind pre (fst es.es_ml) (fst es.es_mr) in
  let post = ts_inv_rebind post (fst es.es_ml) (fst es.es_mr) in
  let cond1, cond2 = conseq_cond_ts (es_pr es) (es_po es) pre post in
  let concl1 = f_forall_mems_ts_inv es.es_ml es.es_mr cond1 in
  let concl2 = f_forall_mems_ts_inv es.es_ml es.es_mr cond2 in
  let concl3 = f_equivS (snd es.es_ml) (snd es.es_mr) pre es.es_sl es.es_sr post in
  FApi.xmutate1 tc `HlConseq [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)
let t_conseq (pre : inv) (post : inv) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node, pre, post with
  | FhoareF hf, Inv_ss pre, Inv_ss post ->
    let epost = (hf_po hf).hsi_inv.exnmap in
    let post = ss_inv_rebind post (hf_po hf).hsi_m in
    let post = { hsi_m = (hf_po hf).hsi_m; hsi_inv = POE.mk post.inv epost} in
    t_hoareF_conseq pre post tc
  | FhoareS hs, Inv_ss pre, Inv_ss post ->
    let epost = (hs_po hs).hsi_inv.exnmap in
    let post = ss_inv_rebind post (hs_po hs).hsi_m in
    let post = { hsi_m = (hs_po hs).hsi_m; hsi_inv = POE.mk post.inv epost } in
    t_hoareS_conseq pre post tc
  | FhoareF _, Inv_ss pre, Inv_hs post ->
    t_hoareF_conseq pre post tc
  | FhoareS _, Inv_ss pre, Inv_hs post ->
    t_hoareS_conseq pre post tc
  | FbdHoareF _, Inv_ss pre, Inv_ss post -> t_bdHoareF_conseq pre post tc
  | FbdHoareS _, Inv_ss pre, Inv_ss post -> t_bdHoareS_conseq pre post tc
  | FeHoareF _ , Inv_ss pre, Inv_ss post -> t_ehoareF_conseq pre post tc
  | FeHoareS _ , Inv_ss pre, Inv_ss post -> t_ehoareS_conseq pre post tc
  | FequivF _  , Inv_ts pre, Inv_ts post -> t_equivF_conseq pre post tc
  | FequivS _  , Inv_ts pre, Inv_ts post -> t_equivS_conseq pre post tc
  | FeagerF _  , Inv_ts pre, Inv_ts post -> t_eagerF_conseq pre post tc
  | _           -> tc_error_noXhl !!tc

(* -------------------------------------------------------------------- *)
(* Non-modification (notmod) variants.                                   *)
(*                                                                       *)
(* These tactics weaken postconditions by generalizing over all program   *)
(* variables modified by the statement/function. The key idea:            *)
(*   If Q does not mention modified variables, then                      *)
(*   {P} c {Q} reduces to: ∀ modified vars, P ⇒ Q                      *)
(*                                                                       *)
(* cond_*_notmod: builds the non-modification condition                  *)
(* t_*_notmod:    applies the notmod rule                                *)
(* t_*_conseq_nm: combines notmod with consequence                       *)
(* -------------------------------------------------------------------- *)


(* Build the non-modification side-condition for equivF:
 * universally quantify the pre-memories, substitute the result variables,
 * then generalize over program variables modified by each procedure.
 * Returns (cond, bound_mems, other_bindings). *)
let cond_equivF_notmod ?(mk_other=false) (tc : tcenv1) (cond : ts_inv) =
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
      mk_bind_pvar ml vresl (pvresl, fsigl.fs_ret) ::
      mk_bind_pvar mr vresr (pvresr, fsigr.fs_ret) ::
      List.flatten [mk_bind_globs env ml bdgl; mk_bind_pvars ml bdel;
                    mk_bind_globs env mr bdgr; mk_bind_pvars mr bder]
    else [] in
  cond, bmem, bother

(* equivF notmod rule:
 *
 *   ∀ml mr, P ml mr ⇒
 *     ∀(res_L : ret_L) (res_R : ret_R) (x1 ... xn : modified vars),
 *       Q' ml mr ⇒ Q ml mr
 *   equiv[f1 ~ f2] P ==> Q'
 *   ——————————————————————————————————————————————————————————————————
 *                    equiv[f1 ~ f2] P ==> Q
 *
 * The first premise universally quantifies over the return values and
 * all program variables modified by f1/f2, then checks that Q' ⇒ Q
 * holds under those bindings. *)
let t_equivF_notmod (post : ts_inv) (tc : tcenv1) =
  let ef = tc1_as_equivF tc in
  let post = ts_inv_rebind post ef.ef_ml ef.ef_mr in
  let cond1, _, _ = cond_equivF_notmod tc (map_ts_inv2 f_imp post (ef_po ef)) in
  let cond2 = f_equivF (ef_pr ef) ef.ef_fl ef.ef_fr post in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let cond_equivS_notmod ?(mk_other=false) (tc : tcenv1) (cond : ts_inv) =
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

(* equivS notmod rule: same as equivF_notmod but for statements
 * (no result variable generalization needed). *)
let t_equivS_notmod (post : ts_inv) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let post = ts_inv_rebind post (fst es.es_ml) (fst es.es_mr) in
  let cond1,_,_ = cond_equivS_notmod tc (map_ts_inv2 f_imp post (es_po es)) in
  let cond2 = f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) es.es_sl es.es_sr post in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
(* Shared core for F-level notmod: substitutes the result variable,     *)
(* generalizes over modified variables, quantifies over the result,     *)
(* and builds the implication with the precondition.                    *)
(*                                                                      *)
(* Returns (cond, bmem, bother) where:                                  *)
(*   cond   : the fully quantified side-condition formula               *)
(*   bmem   : memories bound in the quantification ([m])               *)
(*   bother : when ~mk_other, bindings for result + modified vars;     *)
(*            otherwise []                                              *)

let cond_F_notmod_core
    ~(mk_other : bool)
    (env       : env)
    (hyps      : LDecl.hyps)
    (f         : EcPath.xpath)
    (m         : memory)
    (pre       : ss_inv)
    (cond      : ss_inv)
=
  let mpr,mpo = Fun.hoareF_memenv m f env in
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
  let cond = f_forall_mems_ss_inv mpr (map_ss_inv2 f_imp pre cond) in
  let bmem = [m] in
  let bother =
    if mk_other then
      mk_bind_pvar m vres (pvres, fsig.fs_ret) ::
      List.flatten [mk_bind_globs env m bdg; mk_bind_pvars m bde]
    else [] in
  cond, bmem, bother

let cond_hoareF_notmod ?(mk_other=false) (tc : tcenv1) (cond : ss_inv) =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let hf = tc1_as_hoareF tc in
  cond_F_notmod_core ~mk_other env hyps hf.hf_f hf.hf_m (hf_pr hf) cond

(* hoareF notmod rule:
 *
 *   ∀m, P m ⇒
 *     ∀(res : ret) (x1 ... xn : modified vars),
 *       Q' m ⇒ Q m  [∧ Qe_i' ⇒ Qe_i for each exception]
 *   hoare[f] P ==> Q' / Qe'
 *   ———————————————————————————————————————————————————————
 *                hoare[f] P ==> Q / Qe
 *
 * Q / Qe denotes the normal postcondition Q together with the
 * per-exception postconditions Qe_i (if any). *)
let t_hoareF_notmod (post : hs_inv) (tc : tcenv1) =
  let hf = tc1_as_hoareF tc in
  let p = hs_inv_rebind post hf.hf_m in
  let post, epost = POE.destruct p.hsi_inv in
  let fpost, fepost = POE.destruct (hf_po hf).hsi_inv in
  let cond = f_imp post fpost in
  let econd1 = TTC.merge2_poe_list fepost epost in
  let cond1 = List.fold f_and cond econd1 in
  let cond1, _, _ = cond_hoareF_notmod tc {m=hf.hf_m;inv=cond1} in
  let cond2 = f_hoareF (hf_pr hf) hf.hf_f p in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
(* Shared core for S-level notmod: generalizes over modified variables  *)
(* and builds the implication with the precondition.                    *)

let cond_S_notmod_core
    ~(mk_other : bool)
    (env       : env)
    (stmt      : stmt)
    (memenv    : memenv)
    (pre       : ss_inv)
    (cond      : ss_inv)
=
  let m = fst memenv in
  let modi = s_write env stmt in
  let cond, bdg, bde = generalize_mod_ env modi cond in
  let cond = f_forall_mems_ss_inv memenv (map_ss_inv2 f_imp pre cond) in
  let bmem = [m] in
  let bother =
    if mk_other then
      List.flatten [mk_bind_globs env m bdg; mk_bind_pvars m bde]
    else [] in
  cond, bmem, bother

let cond_hoareS_notmod ?(mk_other=false) (tc : tcenv1) (cond : ss_inv) =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_hoareS tc in
  cond_S_notmod_core ~mk_other env hs.hs_s hs.hs_m (hs_pr hs) cond

(* hoareS notmod rule: same as hoareF_notmod but for statements. *)
let t_hoareS_notmod (post : hs_inv) (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let p = hs_inv_rebind post (fst hs.hs_m) in
  let post, epost = POE.destruct p.hsi_inv in
  let fpost, fepost = POE.destruct (hs_po hs).hsi_inv in
  let cond = f_imp post fpost in
  let econd1 = TTC.merge2_poe_list fepost epost in
  let cond1 = List.fold f_and cond econd1 in
  let cond1, _, _ = cond_hoareS_notmod tc {m=fst hs.hs_m;inv=cond1} in
  let cond2 = f_hoareS (snd hs.hs_m) (hs_pr hs) hs.hs_s p in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let cond_bdHoareF_notmod ?(mk_other=false) (tc : tcenv1) (cond : ss_inv) =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let hf = tc1_as_bdhoareF tc in
  cond_F_notmod_core ~mk_other env hyps hf.bhf_f hf.bhf_m (bhf_pr hf) cond


(* bdHoareF notmod rule:
 *
 *   ∀m, P m ⇒
 *     ∀(res : ret) (x1 ... xn : modified vars),
 *       Q' m ⇒/⇔/⇐ Q m
 *   phoare[f] P ==> Q' cmp bd
 *   ——————————————————————————————————————————————
 *            phoare[f] P ==> Q cmp bd
 *
 * The direction of the postcondition implication depends on cmp:
 *   FHle (≤): Q' ⇒ Q    FHeq (=): Q' ⇔ Q    FHge (≥): Q ⇒ Q' *)
let t_bdHoareF_notmod (post : ss_inv) (tc : tcenv1) =
  let hf = tc1_as_bdhoareF tc in
  let post = ss_inv_rebind post hf.bhf_m in
  let _, cond =
    bdHoare_conseq_conds hf.bhf_cmp (bhf_pr hf) (bhf_po hf) (bhf_pr hf) post in
  let cond1, _, _ = cond_bdHoareF_notmod tc cond in
  let cond2 = f_bdHoareF (bhf_pr hf) hf.bhf_f post hf.bhf_cmp (bhf_bd hf) in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let cond_bdHoareS_notmod ?(mk_other=false) (tc : tcenv1) (cond : ss_inv) =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_bdhoareS tc in
  cond_S_notmod_core ~mk_other env hs.bhs_s hs.bhs_m (bhs_pr hs) cond

(* bdHoareS notmod rule: same as bdHoareF_notmod but for statements. *)
let t_bdHoareS_notmod (post : ss_inv) (tc : tcenv1) =
  let hs = tc1_as_bdhoareS tc in
  let post = ss_inv_rebind post (fst hs.bhs_m) in
  let _, cond =
    bdHoare_conseq_conds hs.bhs_cmp (bhs_pr hs) (bhs_po hs) (bhs_pr hs) post in
  let cond1, _, _ = cond_bdHoareS_notmod tc cond in
  let cond2 = f_bdHoareS (snd hs.bhs_m) (bhs_pr hs) hs.bhs_s post hs.bhs_cmp (bhs_bd hs) in
  FApi.xmutate1 tc `HlNotmod [cond1; cond2]

(* -------------------------------------------------------------------- *)
let gen_conseq_nm
    (tnm  : 'b -> FApi.backward)
    (tc   : 'a -> 'b -> FApi.backward)
    (pre  : 'a)
    (post : 'b)
=
  FApi.t_internal ~info:"generic-conseq-nm" (fun g ->
    let gs =
      (tnm post @+
        [ t_id;
          tc pre post @+ [t_id; t_trivial; t_id] ]) g in
    FApi.t_swap_goals 0 1 gs
  )

let t_hoareF_conseq_nm   = gen_conseq_nm t_hoareF_notmod   t_hoareF_conseq
let t_hoareS_conseq_nm   = gen_conseq_nm t_hoareS_notmod   t_hoareS_conseq
let t_equivF_conseq_nm   = gen_conseq_nm t_equivF_notmod   t_equivF_conseq
let t_equivS_conseq_nm   = gen_conseq_nm t_equivS_notmod   t_equivS_conseq
let t_bdHoareF_conseq_nm = gen_conseq_nm t_bdHoareF_notmod t_bdHoareF_conseq
let t_bdHoareS_conseq_nm = gen_conseq_nm t_bdHoareS_notmod t_bdHoareS_conseq

(* -------------------------------------------------------------------- *)
(* Concavity / Jensen's inequality for ehoare.
 *
 * Given a concave increasing function fc : xreal → xreal:
 *
 *   concave_incr fc                          (g0: fc is concave & increasing)
 *   ∀m, fc(P') m ≤ P m                      (g1: pre-condition)
 *   ∀m, Q m ≤ fc(Q') m                      (g2: post-condition)
 *   ehoare[f] P' ==> Q'                     (g3: inner judgment)
 *   ——————————————————————————————————————
 *   ehoare[f] P ==> Q
 *
 * The idea: E(fc(g2)) ≤ fc(E(g2)) by Jensen, and fc is increasing
 * so fc(E(g2)) ≤ fc(g1), giving {fc(g1)} c {fc(g2)}.               *)

let t_ehoareF_concave
    (fc   : ss_inv)
    (pre  : ss_inv)
    (post : ss_inv)
    (tc   : tcenv1)
=
  let env = FApi.tc1_env tc in
  let hf = tc1_as_ehoareF tc in
  let pre = ss_inv_rebind pre hf.ehf_m in
  let post = ss_inv_rebind post hf.ehf_m in
  let fc = ss_inv_rebind fc hf.ehf_m in
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

(* ehoareS concavity rule: same as ehoareF_concave but for statements. *)
let t_ehoareS_concave
    (fc   : ss_inv)
    (pre  : ss_inv)
    (post : ss_inv)
    (tc   : tcenv1)
=
  let env = FApi.tc1_env tc in
  let hs = tc1_as_ehoareS tc in
  let s = hs.ehs_s in
  let m = fst hs.ehs_m in
  let pre = ss_inv_rebind pre m in
  let post = ss_inv_rebind post m in
  let fc = ss_inv_rebind fc m in
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
let t_ehoareF_conseq_nm (pre : ss_inv) (post : ss_inv) (tc : tcenv1) =
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
let t_ehoareS_conseq_nm (pre : ss_inv) (post : ss_inv) (tc : tcenv1) =
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
(* Process the "concave" tactic for ehoare judgments.                    *)
(*                                                                       *)
(* Parses the concave function fc : xreal → xreal and the proof term    *)
(* (with optional pre/post), then applies t_ehoare*_concave followed    *)
(* by t_concave_incr to discharge the monotonicity side-condition.       *)
(* -------------------------------------------------------------------- *)

let process_concave
    ((info, fc) : pformula option tuple2 gppterm * pformula)
    (tc         : tcenv1)
=
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
(* Cross-logic rules and conjunction.                                    *)
(*                                                                       *)
(* t_hoare*_conseq_bdhoare: reduce hoare to bdhoare (with bound = 1)    *)
(* t_hoare*_conseq_conj:    split hoare via conjunction of specs         *)
(* t_bdHoare*_conseq_conj:  split bdhoare post via conjunction           *)
(* t_equiv*_conseq_conj:    split equiv via conjunction (rel + L + R)    *)
(* t_equiv*_conseq_bd:      reduce equiv to bdhoare on one side          *)
(* t_*_conseq_equiv:        transitivity: reduce hoare/bdhoare/ehoare    *)
(*                          to equiv + hoare on the other program        *)
(* -------------------------------------------------------------------- *)

(* Reduce hoareS to bdHoareS with bound = 1:
 *
 *   phoare[c] P ==> Q = 1
 *   ——————————————————————
 *      hoare[c] P ==> Q                    *)
let t_hoareS_conseq_bdhoare (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let f_r1 = {m=fst hs.hs_m; inv=f_r1} in
  if not (POE.is_empty (hs_po hs).hsi_inv) then
    tc_error !!tc "exception are not supported";
  let post = POE.lower (hs_po hs) in
  let concl1 = f_bdHoareS (snd hs.hs_m) (hs_pr hs) hs.hs_s post FHeq f_r1 in
  FApi.xmutate1 tc `HlConseqBd [concl1]

(* -------------------------------------------------------------------- *)

(* Reduce hoareF to bdHoareF with bound = 1: same rule as hoareS. *)
let t_hoareF_conseq_bdhoare (tc : tcenv1) =
  let hf = tc1_as_hoareF tc in
  let f_r1 = {m=hf.hf_m; inv=f_r1} in
  if not (POE.is_empty (hf_po hf).hsi_inv) then
    tc_error !!tc "exception are not supported";
  let post = POE.lower (hf_po hf) in
  let concl1 = f_bdHoareF (hf_pr hf) hf.hf_f post FHeq f_r1 in
  FApi.xmutate1 tc `HlConseqBd [concl1]

(* -------------------------------------------------------------------- *)

(* hoareS conjunction rule:
 *
 *   hoare[c] P  ==> Q     hoare[c] P' ==> Q'
 *   ——————————————————————————————————————————
 *        hoare[c] P ∧ P' ==> Q ∧ Q'
 *
 * Requires: the goal's pre = P' ∧ P and post = Q' ∧ Q (checked). *)
let t_hoareS_conseq_conj
    (pre   : ss_inv)
    (post  : hs_inv)
    (pre'  : ss_inv)
    (post' : hs_inv)
    (tc    : tcenv1)
=
  let (_, hyps, _) = FApi.tc1_eflat tc in
  let hs = tc1_as_hoareS tc in
  let pre'' = map_ss_inv2 f_and pre' pre in
  let post'' = map_hs_inv2 f_and post' post in
  if not (ss_inv_alpha_eq hyps (hs_pr hs) pre'')
  then tc_error !!tc "invalid pre-condition";
  if not (hs_inv_alpha_eq hyps (hs_po hs) post'')
  then tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareS (snd hs.hs_m) pre hs.hs_s post in
  let concl2 = f_hoareS (snd hs.hs_m) pre' hs.hs_s post' in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)

(* hoareF conjunction rule: same as hoareS_conseq_conj for functions. *)
let t_hoareF_conseq_conj
    (pre   : ss_inv)
    (post  : hs_inv)
    (pre'  : ss_inv)
    (post' : hs_inv)
    (tc    : tcenv1)
=
  let (_, hyps, _) = FApi.tc1_eflat tc in
  let hf = tc1_as_hoareF tc in
  let pre'' = map_ss_inv2 f_and pre' pre in
  let post'' = map_hs_inv2 f_and post' post in
  if not (ss_inv_alpha_eq hyps (hf_pr hf) pre'')
  then tc_error !!tc "invalid pre-condition";
  if not (hs_inv_alpha_eq hyps (hf_po hf) post'')
  then tc_error !!tc "invalid post-condition";
  let concl1 = f_hoareF pre hf.hf_f post in
  let concl2 = f_hoareF pre' hf.hf_f post' in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)

(* bdHoareS conjunction split:
 *
 * When ~add=false — strip a conjunct from the goal postcondition:
 *   the goal has postcondition post', and post is split off as a
 *   hoare side-condition:
 *     hoare[c] P ==> post     phoare[c] P ==> post' ∧ post cmp bd
 *     —————————————————————————————————————————————————————————————
 *                phoare[c] P ==> post' cmp bd
 *
 * When ~add=true — add a conjunct to the goal postcondition:
 *   the goal already has postcondition post' ∧ post, and post is
 *   factored out into a hoare side-condition:
 *     hoare[c] P ==> post     phoare[c] P ==> post' cmp bd
 *     —————————————————————————————————————————————————————
 *            phoare[c] P ==> post' ∧ post cmp bd           *)
let t_bdHoareS_conseq_conj
    ~(add   : bool)
    (post   : ss_inv)
    (post'  : ss_inv)
    (tc     : tcenv1)
=
  let (_, hyps, _) = FApi.tc1_eflat tc in
  let hs = tc1_as_bdhoareS tc in
  let postc = if add then map_ss_inv2 f_and post' post else post' in
  let posth = if add then post' else map_ss_inv2 f_and post' post in
  if not (ss_inv_alpha_eq hyps (bhs_po hs) postc) then
    tc_error !!tc "invalid post-condition";
  let post = empty_hs post in
  let concl1 = f_hoareS (snd hs.bhs_m) (bhs_pr hs) hs.bhs_s post in
  let concl2 = f_bdHoareS (snd hs.bhs_m) (bhs_pr hs) hs.bhs_s posth
                 hs.bhs_cmp (bhs_bd hs) in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)

(* bdHoareF conjunction split: same as bdHoareS_conseq_conj for functions. *)
let t_bdHoareF_conseq_conj
    ~(add   : bool)
    (post   : ss_inv)
    (post'  : ss_inv)
    (tc     : tcenv1)
=
  let (_, hyps, _) = FApi.tc1_eflat tc in
  let hs = tc1_as_bdhoareF tc in
  let post = ss_inv_rebind post hs.bhf_m in
  let post' = ss_inv_rebind post' hs.bhf_m in
  let postc = if add then map_ss_inv2 f_and post' post else post' in
  let posth = if add then post' else map_ss_inv2 f_and post' post in
  if not (ss_inv_alpha_eq hyps (bhf_po hs) postc) then
    tc_error !!tc "invalid post-condition";
  let post = empty_hs post in
  let concl1 = f_hoareF (bhf_pr hs) hs.bhf_f post in
  let concl2 = f_bdHoareF (bhf_pr hs) hs.bhf_f posth hs.bhf_cmp (bhf_bd hs) in
  FApi.xmutate1 tc `HlConseqBd [concl1; concl2]

(* -------------------------------------------------------------------- *)

(* equivS conjunction rule: split an equiv goal into two hoare side-goals
 * and a relational core.
 *
 *   hoare[cL] P1 ==> Q1    hoare[cR] P2 ==> Q2
 *   equiv[cL ~ cR] P' ==> Q'
 *   ——————————————————————————————————————————————
 *   equiv[cL ~ cR] P' ∧ P1 ∧ P2 ==> Q' ∧ Q1 ∧ Q2
 *
 * Requires: goal pre/post match the conjunction (checked). *)
let t_equivS_conseq_conj
    (pre1  : ss_inv)
    (post1 : ss_inv)
    (pre2  : ss_inv)
    (post2 : ss_inv)
    (pre'  : ts_inv)
    (post' : ts_inv)
    (tc    : tcenv1)
=
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
  let post1 = empty_hs post1 in
  let post2 = empty_hs post2 in
  let concl1 = f_hoareS mtl pre1 es.es_sl post1 in
  let concl2 = f_hoareS mtr pre2 es.es_sr post2 in
  let concl3 = f_equivS mtl mtr pre' es.es_sl es.es_sr post' in
  FApi.xmutate1 tc `HlConseqConj [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)

(* equivF conjunction rule: same as equivS_conseq_conj for functions. *)
let t_equivF_conseq_conj
    (pre1  : ss_inv)
    (post1 : ss_inv)
    (pre2  : ss_inv)
    (post2 : ss_inv)
    (pre'  : ts_inv)
    (post' : ts_inv)
    (tc    : tcenv1)
=
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
  let post1 = empty_hs post1 in
  let post2 = empty_hs post2 in

  let concl1 = f_hoareF pre1 ef.ef_fl post1 in
  let concl2 = f_hoareF pre2 ef.ef_fr post2 in
  let concl3 = f_equivF pre' ef.ef_fl ef.ef_fr post' in
  FApi.xmutate1 tc `HlConseqConj [concl1; concl2; concl3]

(* -------------------------------------------------------------------- *)

(* Reduce equivS to bdHoareS on one side.
 *
 * When the other side's statement is empty, the equiv judgment reduces
 * to a single-program bounded hoare judgment:
 *
 *   phoare[c] P ==> Q = 1
 *   ————————————————————————————————
 *   equiv[c ~ skip] P ==> Q         (for side=Left)                   *)
let t_equivS_conseq_bd (side : side) (pr : ss_inv) (po : ss_inv) (tc : tcenv1) =
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
(* Transitivity via equivalence.                                         *)
(*                                                                       *)
(* Reduce a single-program judgment to an equivalence + a judgment on    *)
(* the second program. For hoare/bdhoare/ehoare goals of the form:       *)
(*   {P1} M1 {Q1}                                                       *)
(* We can prove it via:                                                  *)
(*   cond1: ∀m1, P1 m1 ⇒ ∃m2, P m1 m2 ∧ P2 m2 [∧ q m1 = p m2]       *)
(*   cond2: ∀m1 m2, Q m1 m2 ⇒ Q2 m2 ⇒ Q1 m1                          *)
(*   equiv M1 ~ M2 : P ==> Q                                            *)
(*   {P2} M2 {Q2} [R p]                                                 *)
(*                                                                       *)
(* The optional ~bds handles the bound transfer for bdhoare.             *)
(*                                                                       *)
(* transitivity_side_cond: builds cond1 and cond2                        *)
(* t_hoareF_conseq_equiv:  applies the rule for hoare goals              *)
(* t_bdHoareF_conseq_equiv: applies the rule for bdhoare goals           *)
(* t_ehoareF_conseq_equiv: applies the rule for ehoare goals             *)
(* -------------------------------------------------------------------- *)

let transitivity_side_cond
    ?bds
    (hyps : LDecl.hyps)
    prml poml pomr
    (p    : ts_inv)
    (q    : ts_inv)
    (p2   : ss_inv)
    (q2   : ss_inv)
    (p1   : ss_inv)
    (q1   : ss_inv)
=
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

(* hoareF via equivalence:
 *
 *   ∀m1, P1 m1 ⇒ ∃m2, P m1 m2 ∧ P2 m2
 *   ∀m1 m2, Q m1 m2 ⇒ Q2 m2 ⇒ Q1 m1
 *   equiv[M1 ~ M2] P ==> Q    hoare[M2] P2 ==> Q2
 *   —————————————————————————————————————————————————
 *                  hoare[M1] P1 ==> Q1               *)
let t_hoareF_conseq_equiv
    (f2 : EcPath.xpath)
    (p  : ts_inv)
    (q  : ts_inv)
    (p2 : ss_inv)
    (q2 : ss_inv)
    (tc : tcenv1)
=
  let env, hyps, _ = FApi.tc1_eflat tc in
  let hf1 = tc1_as_hoareF tc in
  if not (POE.is_empty (hf_po hf1).hsi_inv) then
    tc_error !!tc "exception are not supported";
  let ef  = f_equivF p hf1.hf_f f2 q in
  let post = empty_hs q2 in
  let hf2 = f_hoareF p2 f2 post in
  let (prml, _prmr), (poml, pomr) = Fun.equivF_memenv p.ml p.mr hf1.hf_f f2 env in
  let post = (hf_po hf1).hsi_inv.main in
  let post = { m = (hf_po hf1).hsi_m; inv = post; } in
  let (cond1, cond2) =
    transitivity_side_cond hyps prml poml pomr p q p2 q2 (hf_pr hf1) post in
  FApi.xmutate1 tc `HoareFConseqEquiv [cond1; cond2; ef; hf2]

(* bdHoareF via equivalence: same as hoareF but with bound transfer.
 *   cond1 additionally requires q m1 = p m2 (bound equality).        *)
let t_bdHoareF_conseq_equiv
    (f2  : EcPath.xpath)
    (p   : ts_inv)
    (q   : ts_inv)
    (p2  : ss_inv)
    (q2  : ss_inv)
    (bd2 : ss_inv)
    (tc  : tcenv1)
=
  let env, hyps, _ = FApi.tc1_eflat tc in
  let hf1 = tc1_as_bdhoareF tc in
  let ef  = f_equivF p hf1.bhf_f f2 q in
  let hf2 = f_bdHoareF p2 f2 q2 hf1.bhf_cmp bd2 in
  let (prml, _prmr), (poml, pomr) = Fun.equivF_memenv p.ml p.mr hf1.bhf_f f2 env in
  let (cond1, cond2) =
    transitivity_side_cond ~bds:(bhf_bd hf1, bd2) hyps prml poml pomr p q p2 q2 (bhf_pr hf1) (bhf_po hf1) in
  FApi.xmutate1 tc `BdHoareFConseqEquiv [cond1; cond2; ef; hf2]


(* ehoareF via equivalence: similar to hoareF but with xreal ordering.
 *   cond1: ∀m1, ∃m2, P1 m1 = -∞ ∨ (P m1 m2 ∧ P2 m2 ≤ P1 m1)
 *   cond2: ∀m1 m2, Q m1 m2 ⇒ Q1 m1 ≤ Q2 m2                        *)
let t_ehoareF_conseq_equiv
    (f2 : EcPath.xpath)
    (p  : ts_inv)
    (q  : ts_inv)
    (p2 : ss_inv)
    (q2 : ss_inv)
    (tc : tcenv1)
=
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
(* High-level consequence dispatcher: shared helpers                     *)
(* -------------------------------------------------------------------- *)

(* Type of proof-term arguments to the high-level consequence dispatcher.
 * Each argument is an optional (proof_term_option * formula) pair:
 * - None means the argument was not provided
 * - Some (pt, f) where pt is the optional proof term and f the formula *)
type hi_arg = (proofterm option * form) option

let t_hi_trivial =
  let t_s = fun tc -> t_simplify ?target:None ~delta:`No tc in
  FApi.t_try (FApi.t_seqs [t_s; t_split; t_fail])

let t_hi_on1    = FApi.t_on1 ~ttout:t_hi_trivial
let t_hi_on1seq = FApi.t_on1seq ~ttout:t_hi_trivial

let t_hi_check_detbound (tc : tcenv1) who (bound : form) =
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

let t_hi_apply_r ((pt, _f) : proofterm option * form) (tc : tcenv1) =
  match pt with
  | Some pt -> EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt tc
  | None    -> EcPhlTAuto.t_hoare_true tc

let t_hi_error
    (concl : form)
    (f1    : hi_arg)
    (f2    : hi_arg)
    (f3    : hi_arg)
    (tc    : tcenv1)
=
  let pp_f_node (f : form) : string =
    match f.f_node with
    | FequivF   _ -> "equivF"
    | FequivS   _ -> "equivS"
    | FhoareF   _ -> "hoareF"
    | FhoareS   _ -> "hoareS"
    | FbdHoareF _ -> "phoareF"
    | FbdHoareS _ -> "phoareS"
    | FeHoareF  _ -> "ehoareF"
    | FeHoareS  _ -> "ehoareS"
    | _           -> "?"
  in
  let pp_opt_f : hi_arg -> string = function
    | None        -> "_"
    | Some (_, f) -> pp_f_node f
  in
  tc_error_lazy !!tc (fun fmt ->
    Format.fprintf fmt
      "do not how to combine %s and %s and %s into %s"
      (pp_opt_f f1) (pp_opt_f f2) (pp_opt_f f3) (pp_f_node concl))

(* -------------------------------------------------------------------- *)
(* hoareS consequence dispatcher.                                        *)
(*                                                                       *)
(* Supported combinations (goal / f1 / f2 / f3):                         *)
(*   hoareS / hoareS   / ⊥       / ⊥  — simple consequence              *)
(*   hoareS / hoareS   / hoareS  / ⊥  — conjunction of two hoare specs   *)
(*   hoareS / bdhoareS / ⊥       / ⊥  — via bounded hoare (bound = 1)   *)
(* -------------------------------------------------------------------- *)

let t_hi_conseq_hoareS
    (notmod : bool)
    (f1     : hi_arg)
    (f2     : hi_arg)
    (f3     : hi_arg)
    (tc     : tcenv1)
=
  let concl = FApi.tc1_goal tc in
  match f1, f2, f3 with
  (* hoareS / hoareS / ⊥ / ⊥ *)
  | Some ((_, {f_node = FhoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_hoareS_conseq_nm else t_hoareS_conseq in
    t_hi_on1 2 (t_hi_apply_r nf1) (tac (hs_pr hs) (hs_po hs) tc)

  (* hoareS / hoareS / hoareS / ⊥ *)
  | Some ((_, { f_node = FhoareS hs }) as nf1),
    Some ((_, f2) as nf2),
    None
    ->
    let hs2 = pf_as_hoareS !!tc f2 in
    let tac = if notmod then t_hoareS_conseq_nm else t_hoareS_conseq in

    t_hi_on1seq 2
      (tac
         (map_ss_inv2 f_and (hs_pr hs) (hs_pr hs2))
         (map_hs_inv2 f_and (hs_po hs) (hs_po hs2))
      )
      (FApi.t_seqsub
         (t_hoareS_conseq_conj
            (hs_pr hs2) (hs_po hs2)
            (hs_pr hs) (hs_po hs))
         [t_hi_apply_r nf2; t_hi_apply_r nf1])
      tc

  (* hoareS / bdhoareS / ⊥ / ⊥ *)
  | Some ((_, {f_node = FbdHoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in

    t_hi_check_detbound tc `First (bhs_bd hs).inv;

    FApi.t_seq
      t_hoareS_conseq_bdhoare
      (t_hi_on1seq 1
         (t_bdHoareS_conseq_bd hs.bhs_cmp (bhs_bd hs))
         (t_hi_on1seq 2 (tac (bhs_pr hs) (bhs_po hs)) (t_hi_apply_r nf1)))
      tc

  | _ -> t_hi_error concl f1 f2 f3 tc

(* -------------------------------------------------------------------- *)
(* hoareF consequence dispatcher.                                        *)
(*                                                                       *)
(* Supported combinations (goal / f1 / f2 / f3):                         *)
(*   hoareF / hoareF   / ⊥       / ⊥  — simple consequence              *)
(*   hoareF / hoareF   / hoareF  / ⊥  — conjunction of two hoare specs   *)
(*   hoareF / bdhoareF / ⊥       / ⊥  — via bounded hoare (bound = 1)   *)
(*   hoareF / equivF   / hoareF  / _  — transitivity via equiv           *)
(* -------------------------------------------------------------------- *)

let t_hi_conseq_hoareF
    (notmod : bool)
    (f1     : hi_arg)
    (f2     : hi_arg)
    (f3     : hi_arg)
    (tc     : tcenv1)
=
  let concl = FApi.tc1_goal tc in
  match f1, f2, f3 with
  (* hoareF / hoareF / ⊥ / ⊥ *)
  | Some ((_, {f_node = FhoareF hs}) as nf1), None, None ->
    let tac = if notmod then t_hoareF_conseq_nm else t_hoareF_conseq in
    t_hi_on1 2 (t_hi_apply_r nf1) (tac (hf_pr hs) (hf_po hs) tc)

  (* hoareF / hoareF / hoareF / ⊥ *)
  | Some ((_, {f_node = FhoareF hf}) as nf1),
    Some((_, f2) as nf2),
    None
    ->
    let hs2 = pf_as_hoareF !!tc f2 in
    let tac = if notmod then t_hoareF_conseq_nm else t_hoareF_conseq in
    let pr1, po1 = hf_pr hf, hf_po hf in
    let pr2 = ss_inv_rebind (hf_pr hs2) hf.hf_m in
    let po2 = hs_inv_rebind (hf_po hs2) hf.hf_m in
    t_hi_on1seq 2
      ((tac
          (map_ss_inv2 f_and pr1 pr2)
          (map_hs_inv2 f_and po1 po2)
       ))
      (FApi.t_seqsub
         (t_hoareF_conseq_conj pr2 po2 pr1 po1)
         [t_hi_apply_r nf2; t_hi_apply_r nf1])
      tc

  (* hoareF / bdhoareF / ⊥ / ⊥ *)
  | Some ((_, {f_node = FbdHoareF hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareF_conseq_nm else t_bdHoareF_conseq in

    t_hi_check_detbound tc `First (bhf_bd hs).inv;

    FApi.t_seq
      t_hoareF_conseq_bdhoare
      (t_hi_on1seq 1
         (t_bdHoareF_conseq_bd hs.bhf_cmp (bhf_bd hs))
         (t_hi_on1seq 2 (tac (bhf_pr hs) (bhf_po hs)) (t_hi_apply_r nf1)))
      tc

  (* hoareF / equivF / hoareF — transitivity via equiv *)
  | Some ((_, {f_node = FequivF ef}) as nef), Some((_, f2) as nf2), _ ->
    let hf2 = pf_as_hoareF !!tc f2 in
    if not (POE.is_empty (hf_po hf2).hsi_inv) then
      tc_error !!tc "exception are not supported";
    let post = POE.lower (hf_po hf2) in
    FApi.t_seqsub
      (t_hoareF_conseq_equiv hf2.hf_f (ef_pr ef) (ef_po ef) (hf_pr hf2) post)
      [t_id; t_id; t_hi_apply_r nef; t_hi_apply_r nf2] tc

  | _ -> t_hi_error concl f1 f2 f3 tc

(* -------------------------------------------------------------------- *)
(* ehoareS consequence dispatcher.                                       *)
(*                                                                       *)
(* Supported combinations (goal / f1 / f2 / f3):                         *)
(*   ehoareS / ehoareS / ⊥ / ⊥  — simple consequence                    *)
(* -------------------------------------------------------------------- *)

let t_hi_conseq_ehoareS
    (notmod : bool)
    (f1     : hi_arg)
    (f2     : hi_arg)
    (f3     : hi_arg)
    (tc     : tcenv1)
=
  let concl = FApi.tc1_goal tc in
  match f1, f2, f3 with
  (* ehoareS / ehoareS / ⊥ / ⊥ *)
  | Some ((_, {f_node = FeHoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_ehoareS_conseq_nm else t_ehoareS_conseq in
    FApi.t_last (t_hi_apply_r nf1) (tac (ehs_pr hs) (ehs_po hs) tc)

  | _ -> t_hi_error concl f1 f2 f3 tc

(* -------------------------------------------------------------------- *)
(* ehoareF consequence dispatcher.                                       *)
(*                                                                       *)
(* Supported combinations (goal / f1 / f2 / f3):                         *)
(*   ehoareF / ehoareF / ⊥      / ⊥  — simple consequence               *)
(*   ehoareF / equivF  / ehoareF / _  — transitivity via equiv           *)
(* -------------------------------------------------------------------- *)

let t_hi_conseq_ehoareF
    (notmod : bool)
    (f1     : hi_arg)
    (f2     : hi_arg)
    (f3     : hi_arg)
    (tc     : tcenv1)
=
  let concl = FApi.tc1_goal tc in
  match f1, f2, f3 with
  (* ehoareF / ehoareF / ⊥ / ⊥ *)
  | Some ((_, {f_node = FeHoareF hf}) as nf1), None, None ->
    let tac = if notmod then t_ehoareF_conseq_nm else t_ehoareF_conseq in
    FApi.t_last (t_hi_apply_r nf1) (tac (ehf_pr hf) (ehf_po hf) tc)

  (* ehoareF / equivF / ehoareF — transitivity via equiv *)
  | Some ((_, {f_node = FequivF ef}) as nef), Some((_, f2) as nf2), _ ->
    let hf2 = pf_as_ehoareF !!tc f2 in
    FApi.t_seqsub
      (t_ehoareF_conseq_equiv hf2.ehf_f (ef_pr ef) (ef_po ef) (ehf_pr hf2) (ehf_po hf2))
      [t_id; t_id; t_hi_apply_r nef; t_hi_apply_r nf2] tc

  | _ -> t_hi_error concl f1 f2 f3 tc

(* -------------------------------------------------------------------- *)
(* bdhoareS consequence dispatcher.                                      *)
(*                                                                       *)
(* Supported combinations (goal / f1 / f2 / f3):                         *)
(*   bdhoareS / bdhoareS / ⊥      / ⊥ — consequence with bound change   *)
(*   bdhoareS / bdhoareS / hoareS / ⊥ — conjunction with hoare side-cond *)
(* -------------------------------------------------------------------- *)

let t_hi_conseq_bdHoareS
    (notmod : bool)
    (f1     : hi_arg)
    (f2     : hi_arg)
    (f3     : hi_arg)
    (tc     : tcenv1)
=
  let concl = FApi.tc1_goal tc in
  match f1, f2, f3 with
  (* bdhoareS / bdhoareS / ⊥ / ⊥ *)
  | Some ((_, {f_node = FbdHoareS hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in

    t_hi_on1seq 1
      (t_bdHoareS_conseq_bd hs.bhs_cmp (bhs_bd hs))
      (t_hi_on1seq 2 (tac (bhs_pr hs) (bhs_po hs)) (t_hi_apply_r nf1))
      tc

  (* bdhoareS / bdhoareS / hoareS / ⊥ *)
  | Some ((_, {f_node = FbdHoareS hs}) as nf1),
    Some ((_, f2) as nf2),
    None
    ->
    let hs0 = pf_as_bdhoareS !!tc concl in
    let hs2 = pf_as_hoareS !!tc f2 in
    let tac = if notmod then t_bdHoareS_conseq_nm else t_bdHoareS_conseq in

    let m,hi,hh, h0 =
      as_seq4 (LDecl.fresh_ids (FApi.tc1_hyps tc) ["&m";"_";"_";"_"]) in
    let pre    = map_ss_inv2 f_and (bhs_pr hs) (hs_pr hs2) in
    let mpre   = Fsubst.f_subst_mem pre.m m pre.inv in
    let post1  = (bhs_po hs0) in
    let post   = (bhs_po hs) in
    if not (POE.is_empty (hs_po hs2).hsi_inv) then
      tc_error !!tc "exception are not supported";
    let posta1 = POE.lower (hs_po hs2) in
    let posta  = map_ss_inv2 f_and post posta1 in

    let concl1 = f_forall_mems_ss_inv hs0.bhs_m (map_ss_inv2 f_imp (bhs_pr hs0) pre) in

    let tc = ( t_cut concl1 @+
        [ t_id;   (* subgoal 1 : pre *)
          t_intro_i hi @!
          t_cut (f_hoareS (snd hs2.hs_m) pre hs2.hs_s (hs_po hs2)) @+ [
            t_hoareS_conseq (hs_pr hs2) (hs_po hs2) @+
                [ EcLowGoal.t_trivial;
                  t_hi_trivial;
                  t_clear hi (* subgoal 2 : hs2 *)];
            t_intro_i hh @!
            (t_bdHoareS_conseq_bd hs.bhs_cmp (bhs_bd hs) @+ [
              t_id; (* subgoal 3 : bound *)
              t_bdHoareS_conseq_conj ~add:false posta1 post1 @+ [
                t_hoareS_conseq pre (hs_po hs2) @+ [
                  t_intros_i [m;h0] @! t_cutdef
                    (ptlocal ~args:[pamemory m; palocal h0] hi)
                    mpre @! EcLowGoal.t_trivial;
                  t_hi_trivial;
                  t_apply_hyp hh];
                tac pre posta @+ [
                  t_apply_hyp hi;
                  t_id; (* subgoal 4 : post *)
                  t_bdHoareS_conseq_conj ~add:true posta1 post @+ [
                    t_apply_hyp hh;
                    t_bdHoareS_conseq (bhs_pr hs) post @+ [
                      EcLowGoal.t_trivial;
                      t_hi_trivial;
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
      [t_hi_trivial; t_hi_trivial; t_hi_trivial; t_hi_apply_r nf2; t_hi_apply_r nf1]
      tc

  | _ -> t_hi_error concl f1 f2 f3 tc

(* -------------------------------------------------------------------- *)
(* bdhoareF consequence dispatcher.                                      *)
(*                                                                       *)
(* Supported combinations (goal / f1 / f2 / f3):                         *)
(*   bdhoareF / bdhoareF / ⊥      / ⊥ — consequence with bound change   *)
(*   bdhoareF / bdhoareF / hoareF / ⊥ — conjunction with hoare side-cond *)
(*   bdhoareF / equivF   / bdhoareF/ _ — transitivity via equiv          *)
(* -------------------------------------------------------------------- *)

let t_hi_conseq_bdHoareF
    (notmod : bool)
    (f1     : hi_arg)
    (f2     : hi_arg)
    (f3     : hi_arg)
    (tc     : tcenv1)
=
  let concl = FApi.tc1_goal tc in
  match f1, f2, f3 with
  (* bdhoareF / bdhoareF / ⊥ / ⊥ *)
  | Some ((_, {f_node = FbdHoareF hs}) as nf1), None, None ->
    let tac = if notmod then t_bdHoareF_conseq_nm else t_bdHoareF_conseq in

    t_hi_on1seq 1
      (t_bdHoareF_conseq_bd hs.bhf_cmp (bhf_bd hs))
      (t_hi_on1seq 2 (tac (bhf_pr hs) (bhf_po hs)) (t_hi_apply_r nf1))
      tc

  (* bdhoareF / bdhoareF / hoareF / ⊥ *)
  | Some ((_, {f_node = FbdHoareF hs}) as nf1),
    Some ((_, f2) as nf2),
    None
    ->
    let hs0 = pf_as_bdhoareF !!tc concl in
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
    if not (POE.is_empty (hf_po hs2).hsi_inv) then
      tc_error !!tc "exception are not supported";
    let posta1 = POE.lower (hf_po hs2) in
    let posta  = map_ss_inv2 f_and post posta1 in
    let mpr,_ = EcEnv.Fun.hoareF_memenv hs0.bhf_m hs0.bhf_f (FApi.tc1_env tc) in

    let concl1 = f_forall_mems_ss_inv mpr (map_ss_inv2 f_imp hs0_pr pre) in

    let tc = ( t_cut concl1 @+
        [ t_id;   (* subgoal 1 : pre *)
          t_intro_i hi @!
          t_cut (f_hoareF pre hs2.hf_f (hf_po hs2)) @+ [
            t_hoareF_conseq (hf_pr hs2) (hf_po hs2) @+
                [ EcLowGoal.t_trivial;
                  t_hi_trivial;
                  t_clear hi (* subgoal 2 : hs2 *)];
            t_intro_i hh @!
            (t_bdHoareF_conseq_bd hs.bhf_cmp (bhf_bd hs) @+ [
              t_id; (* subgoal 3 : bound *)
              t_bdHoareF_conseq_conj ~add:false posta1 post1 @+ [
                t_hoareF_conseq pre (hf_po hs2) @+ [
                  t_intros_i [m;h0] @! t_cutdef
                    (ptlocal ~args:[pamemory m; palocal h0] hi)
                    mpre @! EcLowGoal.t_trivial;
                  t_hi_trivial @! t_intros_i [m; h0] @! t_apply_hyp h0;
                  t_apply_hyp hh];
                tac pre posta @+ [
                  t_apply_hyp hi;
                  t_id; (* subgoal 4 : post *)
                  t_bdHoareF_conseq_conj ~add:true posta1 post @+ [
                    t_apply_hyp hh;
                    t_bdHoareF_conseq (bhf_pr hs) post @+ [
                      EcLowGoal.t_trivial;
                      t_hi_trivial;
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
      [t_hi_trivial; t_hi_trivial; t_hi_trivial; t_hi_apply_r nf2; t_hi_apply_r nf1]
      tc

  (* bdhoareF / equivF / bdhoareF — transitivity via equiv *)
  | Some ((_, {f_node = FequivF ef}) as nef), Some((_, f2) as nf2), _ ->
    let hf2 = pf_as_bdhoareF !!tc f2 in
    FApi.t_seqsub
      (t_bdHoareF_conseq_equiv hf2.bhf_f (ef_pr ef) (ef_po ef)
                                         (bhf_pr hf2) (bhf_po hf2) (bhf_bd hf2))
      [t_id; t_id; t_hi_apply_r nef; t_hi_apply_r nf2] tc

  | _ -> t_hi_error concl f1 f2 f3 tc

(* -------------------------------------------------------------------- *)
(* equivS consequence dispatcher.                                        *)
(*                                                                       *)
(* Supported combinations (goal / f1 / f2 / f3):                         *)
(*   equivS / equivS   / ⊥        / ⊥        — simple consequence       *)
(*   equivS / equivS   / hoareS   / hoareS   — conjunction (rel+L+R)    *)
(*   equivS / equivS   / bdhoareS / ⊥        — recurse on inner bd goal *)
(*   equivS / equivS   / ⊥        / bdhoareS — recurse on inner bd goal *)
(*   equivS / ?        / ?        / ⊥        — fill missing f3 with ⊤   *)
(*   equivS / ?        / ⊥        / ?        — fill missing f2 with ⊤   *)
(*   equivS / ⊥        / bdhoareS / ⊥        — left-side bd equivalence *)
(*   equivS / ⊥        / ⊥        / bdhoareS — right-side bd equivalence*)
(* -------------------------------------------------------------------- *)

let rec t_hi_conseq_equivS
    (notmod : bool)
    (f1     : hi_arg)
    (f2     : hi_arg)
    (f3     : hi_arg)
    (tc     : tcenv1)
=
  let concl = FApi.tc1_goal tc in
  match f1, f2, f3 with
  (* equivS / equivS / ⊥ / ⊥ *)
  | Some ((_, {f_node = FequivS es}) as nf1), None, None ->
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in
    t_hi_on1 2 (t_hi_apply_r nf1) (tac (es_pr es) (es_po es) tc)

  (* equivS / equivS / hoareS / hoareS *)
  | Some ((_, {f_node = FequivS es}) as nf1),
    Some ((_, f2) as nf2),
    Some ((_, f3) as nf3)
    ->
    let hs2    = pf_as_hoareS !!tc f2 in
    let hs3    = pf_as_hoareS !!tc f3 in
    let (ml, mr) = (fst es.es_ml, fst es.es_mr) in

    if not (POE.is_empty (hs_po hs2).hsi_inv) then
      tc_error !!tc "exception are not supported";
    let post2 = POE.lower (hs_po hs2) in
    if not (POE.is_empty (hs_po hs3).hsi_inv) then
      tc_error !!tc "exception are not supported";
    let post3 = POE.lower (hs_po hs3) in

    let hs2_pr = ss_inv_generalize_as_left (hs_pr hs2) ml mr in
    let hs2_po = ss_inv_generalize_as_left post2 ml mr in
    let hs3_pr = ss_inv_generalize_as_right (hs_pr hs3) ml mr in
    let hs3_po = ss_inv_generalize_as_right post3 ml mr in

    let pre    = map_ts_inv f_ands [es_pr es; hs2_pr; hs3_pr] in
    let post   = map_ts_inv f_ands [es_po es; hs2_po; hs3_po] in
    let tac    = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    t_hi_on1seq 2 (tac pre post)
      (FApi.t_seqsub
         (t_equivS_conseq_conj
            (hs_pr hs2) post2 (hs_pr hs3) post3 (es_pr es) (es_po es))
         [t_hi_apply_r nf2; t_hi_apply_r nf3; t_hi_apply_r nf1])
      tc

  (* equivS / equivS / bdhoareS / ⊥ *)
  | Some (_, {f_node = FequivS es}), Some (_, f), None
      when is_bdHoareS f
    ->
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    t_hi_on1seq 2
      (tac (es_pr es) (es_po es))
      (t_hi_conseq_equivS notmod None f2 None)
      tc

  (* equivS / equivS / ⊥ / bdhoareS *)
  | Some (_, {f_node = FequivS es}), None, Some (_, f)
      when is_bdHoareS f
    ->
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    t_hi_on1seq 2
      (tac (es_pr es) (es_po es))
      (t_hi_conseq_equivS notmod None None f3)
      tc

  (* equivS / ? / ? / ⊥ — synthesize missing f3 *)
  | Some _, Some _, None ->
    let es = pf_as_equivS !!tc concl in
    let m = EcIdent.create "&hr" in
    let post = { hsi_m = m; hsi_inv = POE.empty f_true; } in
    let f3 = f_hoareS (snd es.es_mr) {m;inv=f_true} es.es_sr post
    in
    t_hi_conseq_equivS notmod f1 f2 (Some (None, f3)) tc

  (* equivS / ? / ⊥ / ? — synthesize missing f2 *)
  | Some _, None, Some _ ->
    let es = pf_as_equivS !!tc concl in
    let m = EcIdent.create "&hr" in
    let f2 =
      f_hoareS
        (snd es.es_ml) {m;inv=f_true} es.es_sl
        { hsi_m = m; hsi_inv = POE.empty f_true; }
    in
    t_hi_conseq_equivS notmod f1 (Some (None, f2)) f3 tc

  (* equivS / ⊥ / bdhoareS / ⊥ — left-side bounded equivalence *)
  | None, Some ((_, f2) as nf2), None ->
    let es = pf_as_equivS !!tc concl in
    let hs = pf_as_bdhoareS !!tc f2 in
    let (ml, mr) = (fst es.es_ml, fst es.es_mr) in
    let pre = ss_inv_generalize_as_left (bhs_pr hs) ml mr in
    let post = ss_inv_generalize_as_left (bhs_po hs) ml mr in
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    t_hi_check_detbound tc `Second (bhs_bd hs).inv;

    t_hi_on1seq 2
     (tac pre post)
     (FApi.t_seq
        (t_equivS_conseq_bd `Left (bhs_pr hs) (bhs_po hs))
        (t_hi_apply_r nf2))
     tc

  (* equivS / ⊥ / ⊥ / bdhoareS — right-side bounded equivalence *)
  | None, None, Some ((_, f3) as nf3) ->
    let es = pf_as_equivS !!tc concl in
    let hs = pf_as_bdhoareS !!tc f3 in
    let (ml, mr) = (fst es.es_ml, fst es.es_mr) in
    let pre = ss_inv_generalize_as_right (bhs_pr hs) ml mr in
    let post = ss_inv_generalize_as_right (bhs_po hs) ml mr in
    let tac = if notmod then t_equivS_conseq_nm else t_equivS_conseq in

    t_hi_check_detbound tc `Third (bhs_bd hs).inv;

    t_hi_on1seq 2
      (tac pre post)
      (FApi.t_seq
         (t_equivS_conseq_bd `Right (bhs_pr hs) (bhs_po hs))
         (t_hi_apply_r nf3))
      tc

  | _ -> t_hi_error concl f1 f2 f3 tc

(* -------------------------------------------------------------------- *)
(* equivF consequence dispatcher.                                        *)
(*                                                                       *)
(* Supported combinations (goal / f1 / f2 / f3):                         *)
(*   equivF / equivF / ⊥      / ⊥      — simple consequence             *)
(*   equivF / equivF / hoareF / hoareF — conjunction (rel+L+R)          *)
(*   equivF / ?      / ?      / ⊥      — fill missing f3 with ⊤         *)
(*   equivF / ?      / ⊥      / ?      — fill missing f2 with ⊤         *)
(* -------------------------------------------------------------------- *)

let rec t_hi_conseq_equivF
    (notmod : bool)
    (f1     : hi_arg)
    (f2     : hi_arg)
    (f3     : hi_arg)
    (tc     : tcenv1)
=
  let concl = FApi.tc1_goal tc in
  match f1, f2, f3 with
  (* equivF / equivF / ⊥ / ⊥ *)
  | Some ((_, {f_node = FequivF ef}) as nf1), None, None ->
    let tac = if notmod then t_equivF_conseq_nm else t_equivF_conseq in
    t_hi_on1seq 2 (tac (ef_pr ef) (ef_po ef)) (t_hi_apply_r nf1) tc

  (* equivF / equivF / hoareF / hoareF *)
  | Some ((_, {f_node = FequivF ef}) as nf1),
    Some ((_, f2) as nf2),
    Some ((_, f3) as nf3)
    ->
    let hs2    = pf_as_hoareF !!tc f2 in
    let hs3    = pf_as_hoareF !!tc f3 in
    let (ml, mr) = (ef.ef_ml, ef.ef_mr) in

    if not (POE.is_empty (hf_po hs2).hsi_inv) then
      tc_error !!tc "exception are not supported";
    let post2 = POE.lower (hf_po hs2) in
    if not (POE.is_empty (hf_po hs3).hsi_inv) then
      tc_error !!tc "exception are not supported";
    let post3 = POE.lower (hf_po hs3) in

    let hs2_pr = ss_inv_generalize_as_left (hf_pr hs2) ml mr in
    let hs3_pr = ss_inv_generalize_as_right (hf_pr hs3) ml mr in
    let pre    = map_ts_inv f_ands [ef_pr ef; hs2_pr; hs3_pr] in
    let hs2_po = ss_inv_generalize_as_left post2 ml mr in
    let hs3_po = ss_inv_generalize_as_right post3 ml mr in

    let post  = map_ts_inv f_ands [ef_po ef; hs2_po; hs3_po] in
    let tac    = if notmod then t_equivF_conseq_nm else t_equivF_conseq in
    t_hi_on1seq 2
      (tac pre post)
      (FApi.t_seqsub
         (t_equivF_conseq_conj
            (hf_pr hs2) post2 (hf_pr hs3) post3 (ef_pr ef) (ef_po ef))
         [t_hi_apply_r nf2; t_hi_apply_r nf3; t_hi_apply_r nf1])
      tc

  (* equivF / ? / ? / ⊥ — synthesize missing f3 *)
  | Some _, Some _, None ->
    let ef = pf_as_equivF !!tc concl in
    let m = EcIdent.create "&hr" in
    let post = { hsi_m = m; hsi_inv = POE.empty f_true; } in
    let f3 = f_hoareF {m;inv=f_true} ef.ef_fr post in
    t_hi_conseq_equivF notmod f1 f2 (Some (None, f3)) tc

  (* equivF / ? / ⊥ / ? — synthesize missing f2 *)
  | Some _, None, Some _ ->
    let ef = pf_as_equivF !!tc concl in
    let m = EcIdent.create "&hr" in
    let post = { hsi_m = m; hsi_inv = POE.empty f_true; } in
    let f2 = f_hoareF {m;inv=f_true} ef.ef_fl post in
    t_hi_conseq_equivF notmod f1 (Some (None, f2)) f3 tc

  | _ -> t_hi_error concl f1 f2 f3 tc

(* -------------------------------------------------------------------- *)
(* Main high-level consequence dispatcher.                               *)
(*                                                                       *)
(* Dispatches to a goal-type-specific sub-function based on the current  *)
(* goal's formula node type.                                             *)
(* -------------------------------------------------------------------- *)

let t_hi_conseq
    (notmod : bool)
    (f1     : hi_arg)
    (f2     : hi_arg)
    (f3     : hi_arg)
    (tc     : tcenv1)
=
  let concl = FApi.tc1_goal tc in
  match concl.f_node with
  | FhoareS   _ -> t_hi_conseq_hoareS    notmod f1 f2 f3 tc
  | FhoareF   _ -> t_hi_conseq_hoareF    notmod f1 f2 f3 tc
  | FeHoareS  _ -> t_hi_conseq_ehoareS   notmod f1 f2 f3 tc
  | FeHoareF  _ -> t_hi_conseq_ehoareF   notmod f1 f2 f3 tc
  | FbdHoareS _ -> t_hi_conseq_bdHoareS  notmod f1 f2 f3 tc
  | FbdHoareF _ -> t_hi_conseq_bdHoareF  notmod f1 f2 f3 tc
  | FequivS   _ -> t_hi_conseq_equivS    notmod f1 f2 f3 tc
  | FequivF   _ -> t_hi_conseq_equivF   notmod f1 f2 f3 tc
  | _           -> t_hi_error concl f1 f2 f3 tc

(* -------------------------------------------------------------------- *)
type processed_conseq_info =
  | PCI_bd of hoarecmp option * ss_inv

let process_info pe (hyps : LDecl.hyps) (m : memory) = function
  | CQI_bd (cmp, bd) -> PCI_bd (cmp, {m; inv=TTC.pf_process_form pe hyps treal bd})

(* -------------------------------------------------------------------- *)
(* Shared pipeline for processing consequence tactic arguments.          *)
(*                                                                       *)
(* Given closures for processing the primary cut (f1) and secondary cuts *)
(* (f2, f3), this function:                                              *)
(*   1. Parses each argument as a closed proof term via process_cut      *)
(*   2. Dispatches to the high-level consequence tactic t_hi_conseq      *)
(*                                                                       *)
(* The process_cut closures handle goal-type-specific formula building   *)
(* and are provided by process_conseq_hs (for hoare with exceptions)     *)
(* and process_conseq_ss (for all other judgment types).                  *)
(* -------------------------------------------------------------------- *)

let process_conseq_core
    ~process_cut1
    ~process_cut2
    (notmod : bool)
    (info1  : conseq_ppterm option)
    (info2  : conseq_ppterm option)
    (info3  : conseq_ppterm option)
    (tc     : tcenv1)
=
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
(* process_conseq_ss: processes consequence arguments for judgment types  *)
(* with simple (non-exception) postconditions: ehoare, bdhoare, equiv.   *)
(*                                                                       *)
(* Postconditions are Inv_ss (single-state) or Inv_ts (two-state).       *)
(* Exception postconditions (poe) are rejected.                          *)
(* -------------------------------------------------------------------- *)

let process_conseq_ss
    (notmod : bool)
    (infos  : conseq_ppterm option tuple3)
    (tc     : tcenv1)
=
  let (info1, info2, info3) = infos in
  let hyps, concl = FApi.tc1_flat tc in

  let ensure_none o =
    if not (is_none o) then tc_error !!tc "cannot give a bound here" in

  let ensure_none_poe poe =
    if not (is_none poe) then tc_error !!tc "exception are not supported" in

  let process_cut1 ((pre, post, poe), bd) =
     let penv, qenv, gpre, gpost, ty, fmake =
      match concl.f_node with
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

    ensure_none_poe poe;
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

  let process_cut2 side f1 ((pre, post, poe), c_or_bd) =
    let penv, qenv, gpre, gpost, ty, fmake =
      match concl.f_node with
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
          let post = empty_hs post in
          ensure_none c_or_bd; f_hoareS (snd bhs.bhs_m) pre bhs.bhs_s post
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
          let post = empty_hs post in
          ensure_none c_or_bd; f_hoareF pre f post
        in
        (penv, qenv, Inv_ss pr, Inv_ss po, tbool, lift_ss_inv2 fmake)

      | FequivF ef ->
        let f = sideif side ef.ef_fl ef.ef_fr in
        let m = sideif side ef.ef_ml ef.ef_mr in
        let penv, qenv = LDecl.hoareF m f hyps in
        let fmake pre post c_or_bd =
          let post = empty_hs post in
          ensure_none c_or_bd; f_hoareF pre f post
        in
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
            let post = empty_hs post in
            f_hoareS (snd m) pre f post

          | _, Some (PCI_bd (cmp,bd)) ->
            let cmp = odfl FHeq cmp in
            f_bdHoareS (snd m) pre f post cmp bd in
        let f_true = {m=fst m; inv=f_true} in
        (env, env, Inv_ss f_true, Inv_ss f_true, tbool, lift_ss_inv2 fmake)

      | _ -> tc_error !!tc "conseq: not a phl/prhl judgement"
    in

    ensure_none_poe poe;
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

  process_conseq_core ~process_cut1 ~process_cut2 notmod info1 info2 info3 tc

(* -------------------------------------------------------------------- *)
(* process_conseq_hs: processes consequence arguments for hoare          *)
(* judgments (hoareS, hoareF) which have exception-aware postconditions.  *)
(*                                                                       *)
(* Postconditions are Inv_hs (with exception maps via POE).              *)
(* Exception postconditions (poe) are processed via TTC.pf_process_poe.  *)
(* -------------------------------------------------------------------- *)

let process_conseq_hs
    (notmod : bool)
    (infos  : conseq_ppterm option tuple3)
    (tc     : tcenv1)
=
  let (info1, info2, info3) = infos in
  let hyps, concl = FApi.tc1_flat tc in

  let ensure_none o =
    if not (is_none o) then tc_error !!tc "cannot give a bound here" in

  let process_cut1 ((pre, post, poe), bd) =
     let penv, qenv, env_e, gpre, gpost, ty, fmake =
      match concl.f_node with
      | FhoareS hs ->
        let env = LDecl.push_active_ss hs.hs_m hyps in
        let m,_ = hs.hs_m in
        let env_e = LDecl.inv_memenv1 m hyps in

        let fmake pre post c_or_bd =
          match c_or_bd with
          | None ->
            f_hoareS(snd hs.hs_m) pre hs.hs_s post
          | Some (PCI_bd (cmp, bd)) ->
            if not (POE.is_empty post.hsi_inv) then
              tc_error !!tc "exception are not supported";
            let post = POE.lower post in
            f_bdHoareS (snd hs.hs_m) pre hs.hs_s post (oget cmp) bd
        in
        (env, env, env_e,
         Inv_ss (hs_pr hs), Inv_hs (hs_po hs),
         tbool, lift_hs_ss_inv fmake)

      | FhoareF hf ->
        let penv, qenv = LDecl.hoareF hf.hf_m hf.hf_f hyps in
        let env_e = LDecl.inv_memenv1 hf.hf_m hyps in

        let fmake pre post c_or_bd =
          match c_or_bd with
          | None ->
            f_hoareF pre hf.hf_f post
          | Some (PCI_bd (cmp, bd)) ->
            if not (POE.is_empty post.hsi_inv) then
              tc_error !!tc "exception are not supported";
            let post = POE.lower post in
            f_bdHoareF pre hf.hf_f post (oget cmp) bd
        in
        (penv, qenv, env_e,
         Inv_ss (hf_pr hf), Inv_hs (hf_po hf),
         tbool, lift_hs_ss_inv fmake)

      | _ -> tc_error !!tc "conseq: not a phl/prhl judgement"
    in

    let pre  = pre  |> omap (TTC.pf_process_form !!tc penv ty) |> odfl (inv_of_inv gpre) in
    let post  = post  |> omap (TTC.pf_process_form !!tc qenv ty) in
    let poe  = poe |> omap (TTC.pf_process_poe env_e)  in

    let (pre, post, bd) = match gpre, gpost with
      | Inv_ss gpre, Inv_hs gpost ->
        let bd = bd |> omap (process_info !!tc penv gpre.m) in
        let gp, gpoe = POE.destruct gpost.hsi_inv in
        let post = post |> odfl gp in
        let poe = poe |> odfl gpoe in
        (
          Inv_ss { inv = pre; m = gpre.m; },
          Inv_hs { hsi_inv = POE.mk post poe; hsi_m = gpost.hsi_m },
          bd
        )
      | _ -> tc_error !!tc "conseq: pre and post must be of the same kind"
    in
    fmake pre post bd

  in

  let process_cut2 side f1 ((pre, post, poe), bd) =
    let penv, qenv, env_e, gpre, gpost, ty, fmake =
      match concl.f_node with
      | FhoareS hs ->
        let env = LDecl.push_active_ss hs.hs_m hyps in
        let m,_ = hs.hs_m in
        let env_e = LDecl.inv_memenv1 m hyps in
        let fmake pre post c_or_bd =
          ensure_none c_or_bd;
          f_hoareS (snd hs.hs_m) pre hs.hs_s post
        in
        (env, env, env_e,
         Inv_ss (hs_pr hs), Inv_hs (hs_po hs),
         tbool, lift_hs_ss_inv fmake)

      | FhoareF hf ->
        let m = hf.hf_m in
        let f, pr, po = match f1 with
        | None -> hf.hf_f, hf_pr hf, hf_po hf
        | Some f1 ->
          match (snd f1).f_node with
          | FequivF ef when side = `Left ->
            ef.ef_fr, {m; inv=f_true}, {hsi_m=m; hsi_inv=POE.empty f_true}
          | _ -> hf.hf_f, hf_pr hf, hf_po hf
        in
        let penv, qenv = LDecl.hoareF m f hyps in
        let env_e = LDecl.inv_memenv1 m hyps in
        let fmake pre post c_or_bd =
          ensure_none c_or_bd; f_hoareF pre f post
        in
        (penv, qenv, env_e, Inv_ss pr, Inv_hs po, tbool, lift_hs_ss_inv fmake)

      | _ -> tc_error !!tc "conseq: not a phl/prhl judgement"
    in

    let pre  = pre  |> omap (TTC.pf_process_form !!tc penv ty) |> odfl (inv_of_inv gpre)  in
    let post  = post  |> omap (TTC.pf_process_form !!tc qenv ty) in
    let poe  = poe |> omap (TTC.pf_process_poe env_e) in

    let (pre, post, bd) = match gpre, gpost with
      | Inv_ss gpre, Inv_hs gpost ->
        let bd = bd |> omap (process_info !!tc penv gpre.m) in
        let gp, gpoe = POE.destruct gpost.hsi_inv in
        let post = post |> odfl gp in
        let poe = poe |> odfl gpoe in
        (
          Inv_ss { inv = pre; m = gpre.m; },
          Inv_hs { hsi_inv = POE.mk post poe; hsi_m = gpost.hsi_m; },
          bd
        )
      | _ -> tc_error !!tc "conseq: pre and post must be of the same kind"
    in
    fmake pre post bd

  in

  process_conseq_core ~process_cut1 ~process_cut2 notmod info1 info2 info3 tc

let process_conseq
    (notmod : bool)
    (infos  : conseq_ppterm option tuple3)
    (tc     : tcenv1)
=
  let _, concl = FApi.tc1_flat tc in

  match concl.f_node with
  | FhoareS _ | FhoareF _ -> process_conseq_hs notmod infos tc
  | _ -> process_conseq_ss notmod infos tc

(* -------------------------------------------------------------------- *)
let process_bd_equiv (side : side) ((pr, po) : pformula pair) (tc : tcenv1) =
  let info = FPCut ((Some pr, Some po, None), None) in
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
let process_conseq_opt
    (cqopt : pcqoptions)
    (infos : conseq_ppterm option tuple3)
    (tc    : tcenv1)
=
  let cqopt = CQOptions.merge CQOptions.default cqopt in
  process_conseq cqopt.cqo_frame infos tc

(* -------------------------------------------------------------------- *)
(* Automatic consequence (conseqauto).                                   *)
(*                                                                       *)
(* Automatically weakens the postcondition using non-modification:       *)
(* 1. Compute the notmod condition and variable bindings for the goal    *)
(* 2. Start a scratch proof of the notmod condition                      *)
(* 3. Introduce memory/variable bindings & crush forward hypotheses      *)
(* 4. If the scratch proof closes, postcondition becomes ⊤              *)
(*    Otherwise, extract the remaining goal as the new postcondition     *)
(* 5. Apply t_notmod with the computed postcondition, then try to crush  *)
(* -------------------------------------------------------------------- *)

let t_conseqauto ?(delta : bool = true) ?tsolve (tc : tcenv1) =
  let (hyps, concl), mk_other = FApi.tc1_flat tc, true in

  let t_hoareF_notmod f = t_hoareF_notmod (POE.lift f) in
  let t_hoareS_notmod f = t_hoareS_notmod (POE.lift f) in

  let todo =
    match concl.f_node with
    | FhoareF hf when (POE.is_empty (hf_po hf).hsi_inv) ->
      Some (lift_ss_inv t_hoareF_notmod, cond_hoareF_notmod ~mk_other tc (POE.lower (hf_po hf)))
    | FhoareS hs when (POE.is_empty (hs_po hs).hsi_inv) ->
      Some (lift_ss_inv t_hoareS_notmod, cond_hoareS_notmod ~mk_other tc (POE.lower (hs_po hs)))
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
