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
(* The ehoare [fun-def] rule has no parameters. *)
type EcCoreGoal.rule += REHoareFunDef

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (the
   procedure is concrete) is part of it, so the checker re-validates it. *)
let ehoareF_fun_def_subgoals (hyps : LDecl.hyps) (hf : eHoareF) : form list =
  let env = LDecl.toenv hyps in
  let f = NormMp.norm_xfun env hf.ehf_f in
  EcPlFun.ensure_concrete "ehoareF-fun-def" env f;
  let (memenv, (fsig, fdef), env) = Fun.hoareS hf.ehf_m f env in
  let m = EcMemory.memory memenv in
  let fres = odfl {m;inv=f_tt} (omap (ss_inv_of_expr m) fdef.f_ret) in
  let post = map_ss_inv2 (PVM.subst1 env pv_res m) fres (ehf_po hf) in
  let pre  = map_ss_inv1 (PVM.subst env (EcPlFun.subst_pre env fsig m PVM.empty)) (ehf_pr hf) in
  [f_eHoareS (snd memenv) pre fdef.f_body post]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_ehoareF_fun_def (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hf  = tc1_as_ehoareF tc in
  EcPlFun.check_concrete !!tc env (NormMp.norm_xfun env hf.ehf_f);
  FApi.xrule1 tc REHoareFunDef (ehoareF_fun_def_subgoals (FApi.tc1_hyps tc) hf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareFunDef ->
         Some (EcPlRecheck.checker_of "ehoareF-fun-def" pf_as_ehoareF
                 ehoareF_fun_def_subgoals)
     | _ -> None)
