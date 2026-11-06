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
(* The bdhoare [fun-def] rule has no parameters. *)
type EcCoreGoal.rule += RBdHoareFunDef

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (the
   procedure is concrete) is part of it, so the checker re-validates it. *)
let bdhoareF_fun_def_subgoals (hyps : LDecl.hyps) (bhf : bdHoareF) : form list =
  let env = LDecl.toenv hyps in
  let f = NormMp.norm_xfun env bhf.bhf_f in
  EcPlFun.ensure_concrete "bdhoareF-fun-def" env f;
  let (memenv, (fsig, fdef), env) = Fun.hoareS bhf.bhf_m f env in
  let m = EcMemory.memory memenv in
  let fres = odfl {m;inv=f_tt} (omap (ss_inv_of_expr m) fdef.f_ret) in
  let post = map_ss_inv2 (PVM.subst1 env pv_res m) fres (bhf_po bhf) in
  let spre = EcPlFun.subst_pre env fsig m PVM.empty in
  let pre  = map_ss_inv1 (PVM.subst env spre) (bhf_pr bhf) in
  let bd   = map_ss_inv1 (PVM.subst env spre) (bhf_bd bhf) in
  [f_bdHoareS (snd memenv) pre fdef.f_body post bhf.bhf_cmp bd]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_bdhoareF_fun_def (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in
  EcPlFun.check_concrete !!tc env (NormMp.norm_xfun env bhf.bhf_f);
  FApi.xrule1 tc RBdHoareFunDef (bdhoareF_fun_def_subgoals (FApi.tc1_hyps tc) bhf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareFunDef ->
         Some (EcPlRecheck.checker_of "bdhoareF-fun-def" pf_as_bdhoareF
                 bdhoareF_fun_def_subgoals)
     | _ -> None)
