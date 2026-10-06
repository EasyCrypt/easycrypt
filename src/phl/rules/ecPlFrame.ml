(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcTypes
open EcFol
open EcEnv
open EcPV
open EcSubst
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Framing conditions, shared by the frame rules of every logic (and by
   [conseq auto]). Framing — generalizing a condition over the variables a
   program writes — is done here and nowhere else.

   Each builder returns [(cond, bmem, bother)]: the closed side condition,
   the memories it quantifies over, and (only when [~mk_other]) bindings for
   the other quantified variables (result, modified globals and variables),
   used by [conseq auto] to introduce them. *)

type frame_cond = form * memory list * (EcIdent.t * ss_inv) list

(* -------------------------------------------------------------------- *)
(* One-sided, statement: forall &m, pre => forall (mod s), cond. *)
let ss_frame_cond_S
    ~(mk_other : bool)
    (env       : env)
    (s         : stmt)
    (memenv    : memenv)
    (pre       : ss_inv)
    (cond      : ss_inv)
=
  let m = fst memenv in
  let modi = s_write env s in
  let cond, bdg, bde = generalize_mod_ env modi cond in
  let cond = f_forall_mems_ss_inv memenv (map_ss_inv2 f_imp pre cond) in
  let bmem = [m] in
  let bother =
    if mk_other then
      List.flatten [mk_bind_globs env m bdg; mk_bind_pvars m bde]
    else [] in
  cond, bmem, bother

(* -------------------------------------------------------------------- *)
(* One-sided, procedure:
   forall &m, pre => forall (res : ret) (mod f), cond[res/result]. *)
let ss_frame_cond_F
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

(* -------------------------------------------------------------------- *)
(* Two-sided, statements:
   forall &1 &2, pre => forall (mod sl)<1> (mod sr)<2>, cond. *)
let ts_frame_cond_S
    ~(mk_other : bool)
    (env       : env)
    (es        : equivS)
    (cond      : ts_inv)
=
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

(* -------------------------------------------------------------------- *)
(* Two-sided, procedures:
   forall &1 &2, pre =>
     forall (res_L : retl) (res_R : retr) (mod fl)<1> (mod fr)<2>,
       cond[res_L/result<1>, res_R/result<2>]. *)
let ts_frame_cond_F
    ~(mk_other : bool)
    (env       : env)
    (hyps      : LDecl.hyps)
    (ef        : equivF)
    (cond      : ts_inv)
=
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
