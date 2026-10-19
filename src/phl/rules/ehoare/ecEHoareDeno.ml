(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes
open EcFol
open EcEnv
open EcPV
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the ehoare [deno] rule: the pre- and postcondition of
   the judgement on the procedure, in one memory. Already typed, nothing
   to resolve: the same record is the rule argument and the node
   payload. *)
type ehoare_deno = {
  ehd_pre  : ss_inv;    (* P *)
  ehd_post : ss_inv;    (* Q *)
}

type EcCoreGoal.rule += REHoareDeno of ehoare_deno

(* -------------------------------------------------------------------- *)
(* The goals the rule applies to: [Pr[...] <= d]. *)
let destr_deno_goal (concl : form) =
  match concl.f_node with
  | Fapp ({f_node = Fop (op, _)}, [f; bd])
      when is_pr f && EcPath.p_equal op EcCoreLib.CI_Real.p_real_le ->
    Some (destr_pr f, bd)

  | _ -> None

(* [P] and [Q] share their memory, which does not occur free in the goal
   (it is bound around the event of the goal in the third premise). *)
let valid_memories (concl : form) (n : ehoare_deno) =
     EcIdent.id_equal n.ehd_pre.m n.ehd_post.m
  && not (EcIdent.Mid.mem n.ehd_pre.m concl.f_fv)

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   shape of the goal and the memories of [P] and [Q]) are part of it, so
   the checker re-validates them. *)
let ehoare_deno_subgoals (hyps : LDecl.hyps) (concl : form) (n : ehoare_deno) =
  let env = LDecl.toenv hyps in
  let pr, bd =
    match destr_deno_goal concl with
    | Some x -> x
    | None   -> failwith "ehoare-deno: invalid goal shape" in
  if not (valid_memories concl n) then
    failwith "ehoare-deno: invalid memories";
  let m = n.ehd_pre.m in
  let concl_e = f_eHoareF n.ehd_pre pr.pr_fun n.ehd_post in
  let _, mpo = Fun.hoareF_memenv m pr.pr_fun env in

  (* P <= d, with the arguments and the initial memory of the goal *)
  let sargs = PVM.add env pv_arg m pr.pr_args PVM.empty in
  let smem = Fsubst.f_bind_mem Fsubst.f_subst_id m pr.pr_mem in
  let pre = Fsubst.f_subst smem (PVM.subst env sargs n.ehd_pre.inv) in
  let concl_pr = f_xreal_le pre (f_r2xr bd) in

  (* forall &m, E%xr <= Q *)
  let ev = ss_inv_rebind pr.pr_event m in
  let concl_po = map_ss_inv2 f_xreal_le (map_ss_inv1 f_b2xr ev) n.ehd_post in
  let concl_po = f_forall_mems_ss_inv mpo concl_po in

  (* 0%r <= d *)
  let concl_nn = f_real_le f_r0 bd in

  [concl_e; concl_pr; concl_po; concl_nn]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_ehoare_deno (r : ehoare_deno) (tc : tcenv1) =
  let concl = FApi.tc1_goal tc in
  if Option.is_none (destr_deno_goal concl) then
    tc_error !!tc "invalid goal shape";
  if not (valid_memories concl r) then
    tc_error !!tc "invalid memories for the expectation judgement";
  FApi.xrule1 tc (REHoareDeno r)
    (ehoare_deno_subgoals (FApi.tc1_hyps tc) concl r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareDeno n ->
         Some (EcPlRecheck.checker_of "ehoare-deno" (fun _ concl -> concl)
                 (fun hyps concl -> ehoare_deno_subgoals hyps concl n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Elaboration: the judgement is given by a proof term, or cut from the
   goal (precondition the bound and postcondition the event by default),
   then the rule is applied, its first premise closed with it, and its
   last premise [0%r <= d] closed when trivial (a genuinely negative
   bound is left as an unprovable goal). *)
let process_ehoare_deno (info : deno_ppterm) (tc : tcenv1) =
  let error () =
    tc_error !!tc "the conclusion is not a suitable Pr expression" in

  let process_cut (pre, post) =
    let hyps, concl = FApi.tc1_flat tc in
    let f, bd =
      match concl.f_node with
      | Fapp({f_node = Fop (op, _)}, [f1; f2])
          when EcPath.p_equal op EcCoreLib.CI_Real.p_real_le && is_pr f1 ->
          (f1, f2) (* f1 <= f2 *)
      | _ -> error ()
    in

    let { pr_fun = f } as pr = destr_pr f in
    let event = pr.pr_event in
    let m = event.m in
    let penv, qenv = LDecl.hoareF m f hyps in
    let smem = Fsubst.f_bind_mem Fsubst.f_subst_id pr.pr_mem m in
    let dpre = { m; inv = f_r2xr (Fsubst.f_subst smem bd); } in

    let pre  = pre  |> omap_dfl (fun p -> { m; inv = TTC.pf_process_xreal !!tc penv p; }) dpre  in
    let post = post |> omap_dfl (fun p -> { m; inv = TTC.pf_process_xreal !!tc qenv p; }) (map_ss_inv1 f_b2xr event) in

    f_eHoareF pre f post
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:process_cut tc info in

  let hf = pf_as_ehoareF !!tc ax in

  FApi.t_last (FApi.t_try t_trivial)
    (FApi.t_first
       (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt)
       (t_ehoare_deno { ehd_pre = ehf_pr hf; ehd_post = ehf_po hf; } tc))
