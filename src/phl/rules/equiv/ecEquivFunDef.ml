(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcAst
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The equiv [fun-def] rule has no parameters. *)
type EcCoreGoal.rule += REquivFunDef

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (both
   procedures are concrete) is part of it, so the checker re-validates
   it. *)
let equivF_fun_def_subgoals (hyps : LDecl.hyps) (ef : equivF) : form list =
  let env = LDecl.toenv hyps in
  let ml, mr = ef.ef_ml, ef.ef_mr in
  let fl = NormMp.norm_xfun env ef.ef_fl in
  let fr = NormMp.norm_xfun env ef.ef_fr in
  EcPlFun.ensure_concrete "equivF-fun-def" env fl;
  EcPlFun.ensure_concrete "equivF-fun-def" env fr;
  let (menvl, eqsl, menvr, eqsr, env) = Fun.equivS ml mr fl fr env in
  let (fsigl, fdefl) = eqsl in
  let (fsigr, fdefr) = eqsr in
  let fresl = odfl {m=ml;inv=f_tt} (omap (ss_inv_of_expr ml) fdefl.f_ret) in
  let fresr = odfl {m=mr;inv=f_tt} (omap (ss_inv_of_expr mr) fdefr.f_ret) in
  let s = PVM.add env pv_res ml fresl.inv PVM.empty in
  let s = PVM.add env pv_res mr fresr.inv s in
  let post = map_ts_inv1 (PVM.subst env s) (ef_po ef) in
  let s = EcPlFun.subst_pre env fsigl ml PVM.empty in
  let s = EcPlFun.subst_pre env fsigr mr s in
  let pre = map_ts_inv1 (PVM.subst env s) (ef_pr ef) in
  [f_equivS (snd menvl) (snd menvr) pre fdefl.f_body fdefr.f_body post]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_equivF_fun_def (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let ef  = tc1_as_equivF tc in
  EcPlFun.check_concrete !!tc env (NormMp.norm_xfun env ef.ef_fl);
  EcPlFun.check_concrete !!tc env (NormMp.norm_xfun env ef.ef_fr);
  FApi.xrule1 tc REquivFunDef (equivF_fun_def_subgoals (FApi.tc1_hyps tc) ef)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivFunDef ->
         Some (EcPlRecheck.checker_of "equivF-fun-def" pf_as_equivF
                 equivF_fun_def_subgoals)
     | _ -> None)
