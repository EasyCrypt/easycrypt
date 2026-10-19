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
(* The hoare [fun-def] rule has no parameters. *)
type EcCoreGoal.rule += RHoareFunDef

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (the
   procedure is concrete) is part of it, so the checker re-validates it. *)
let hoareF_fun_def_subgoals (hyps : LDecl.hyps) (hf : sHoareF) : form list =
  let env = LDecl.toenv hyps in
  let f = NormMp.norm_xfun env hf.hf_f in
  EcPlFun.ensure_concrete "hoareF-fun-def" env f;
  let (memenv, (fsig, fdef), env) = Fun.hoareS hf.hf_m f env in
  let m = EcMemory.memory memenv in
  let fres = odfl {m;inv=f_tt} (omap (ss_inv_of_expr m) fdef.f_ret) in
  let post, epost = POE.destruct (hf_po hf).hsi_inv in
  let post = {m=(hf_po hf).hsi_m;inv=post} in
  let post = map_ss_inv2 (PVM.subst1 env pv_res m) fres post in
  let pre  = map_ss_inv1 (PVM.subst env (EcPlFun.subst_pre env fsig m PVM.empty)) (hf_pr hf) in
  let post = { hsi_m = post.m; hsi_inv = POE.mk post.inv epost; } in
  [f_hoareS (snd memenv) pre fdef.f_body post]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoareF_fun_def (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hf  = tc1_as_hoareF tc in
  EcPlFun.check_concrete !!tc env (NormMp.norm_xfun env hf.hf_f);
  FApi.xrule1 tc RHoareFunDef (hoareF_fun_def_subgoals (FApi.tc1_hyps tc) hf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareFunDef ->
         Some (EcPlRecheck.checker_of "hoareF-fun-def" pf_as_hoareF
                 hoareF_fun_def_subgoals)
     | _ -> None)
