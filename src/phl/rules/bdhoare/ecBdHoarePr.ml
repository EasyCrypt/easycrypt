(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The bdhoare [pr] rule has no parameters. *)
type EcCoreGoal.rule += RBdHoareFPr

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. The memory [&m] the
   premise quantifies over is fresh at each call: the checker compares up
   to alpha-conversion. *)
let bdhoareF_pr_subgoals (hyps : LDecl.hyps) (bhf : bdHoareF) : form list =
  let env  = LDecl.toenv hyps in
  let fun_ = Fun.by_xpath bhf.bhf_f env in
  let penv, _ = Fun.hoareF_memenv bhf.bhf_m bhf.bhf_f env in
  let m    = EcIdent.create "&hr" in
  let args = map_ss_inv1 (pr_args_of_fun fun_) (f_pvarg fun_.f_sig.fs_arg m) in
  let fop  =
    match bhf.bhf_cmp with
    | FHle -> f_real_le
    | FHge -> fun x y -> f_real_le y x
    | FHeq -> f_eq
  in
  let bd    = ss_inv_rebind (bhf_bd bhf) m in
  let pr    = map_ss_inv1 (fun args -> f_pr m bhf.bhf_f args (bhf_po bhf)) args in
  let concl = map_ss_inv2 fop pr bd in
  let concl = map_ss_inv2 f_imp (ss_inv_rebind (bhf_pr bhf) m) concl in
  let concl = map_ss_inv2 f_and (map_ss_inv1 (f_real_le f_r0) bd) concl in
  [f_forall_mems_ss_inv (m, snd penv) concl]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_bdhoareF_pr (tc : tcenv1) =
  let bhf = tc1_as_bdhoareF tc in
  FApi.xrule1 tc RBdHoareFPr (bdhoareF_pr_subgoals (FApi.tc1_hyps tc) bhf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareFPr ->
         Some (EcPlRecheck.checker_of "bdhoareF-pr" pf_as_bdhoareF
                 (fun hyps bhf -> bdhoareF_pr_subgoals hyps bhf))
     | _ -> None)
