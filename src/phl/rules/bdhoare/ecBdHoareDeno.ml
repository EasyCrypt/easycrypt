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
(* Parameters of the bdhoare [deno] rule: the pre- and postcondition of
   the judgement on the procedure, in one memory. Already typed, nothing
   to resolve: the same record is the rule argument and the node
   payload. *)
type bdhoare_deno = {
  bdd_pre  : ss_inv;    (* P *)
  bdd_post : ss_inv;    (* Q *)
}

type EcCoreGoal.rule += RBdHoareDeno of bdhoare_deno

(* -------------------------------------------------------------------- *)
(* The goals the rule applies to: [Pr[...] <= d], [d <= Pr[...]] and
   [Pr[...] = d], with the comparison they state. *)
let destr_deno_goal (concl : form) =
  match concl.f_node with
  | Fapp ({f_node = Fop (op, _)}, [f; bd])
      when is_pr f && EcPath.p_equal op EcCoreLib.CI_Real.p_real_le ->
    Some (FHle, destr_pr f, bd)

  | Fapp ({f_node = Fop (op, _)}, [bd; f])
      when is_pr f && EcPath.p_equal op EcCoreLib.CI_Real.p_real_le ->
    Some (FHge, destr_pr f, bd)

  | Fapp ({f_node = Fop (op, _)}, [f; bd])
      when is_pr f && EcPath.p_equal op EcCoreLib.CI_Bool.p_eq ->
    Some (FHeq, destr_pr f, bd)

  | _ -> None

(* [P] and [Q] share their memory, which does not occur free in the goal
   (it is bound by the judgement of the premise, around the bound [d]). *)
let valid_memories (concl : form) (n : bdhoare_deno) =
     EcIdent.id_equal n.bdd_pre.m n.bdd_post.m
  && not (EcIdent.Mid.mem n.bdd_pre.m concl.f_fv)

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   shape of the goal and the memories of [P] and [Q]) are part of it, so
   the checker re-validates them. *)
let bdhoare_deno_subgoals (hyps : LDecl.hyps) (concl : form) (n : bdhoare_deno) =
  let env = LDecl.toenv hyps in
  let cmp, pr, bd =
    match destr_deno_goal concl with
    | Some x -> x
    | None   -> failwith "bdhoare-deno: invalid goal shape" in
  if not (valid_memories concl n) then
    failwith "bdhoare-deno: invalid memories";
  let m = n.bdd_pre.m in
  let concl_e = f_bdHoareF n.bdd_pre pr.pr_fun n.bdd_post cmp { m; inv = bd; } in
  let fun_ = Fun.by_xpath pr.pr_fun env in

  (* P, with the arguments and the initial memory of the goal *)
  let sargs = PVM.add env pv_arg m pr.pr_args PVM.empty in
  let smem = Fsubst.f_bind_mem Fsubst.f_subst_id m pr.pr_mem in
  let concl_pr = Fsubst.f_subst smem (PVM.subst env sargs n.bdd_pre.inv) in

  (* Q relates to the event of the goal, in every final memory *)
  let ev = pr.pr_event in
  let me = Fun.actmem_post ev.m fun_ in
  let post = ss_inv_rebind n.bdd_post ev.m in
  let concl_po =
    match cmp with
    | FHle -> map_ss_inv2 f_imp_simpl ev post
    | FHge -> map_ss_inv2 f_imp_simpl post ev
    | FHeq -> map_ss_inv2 f_iff_simpl ev post in
  let concl_po = f_forall_mems_ss_inv me concl_po in

  [concl_e; concl_pr; concl_po]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_bdhoare_deno (r : bdhoare_deno) (tc : tcenv1) =
  let concl = FApi.tc1_goal tc in
  if Option.is_none (destr_deno_goal concl) then
    tc_error !!tc "invalid goal shape";
  if not (valid_memories concl r) then
    tc_error !!tc "invalid memories for the probabilistic judgement";
  FApi.xrule1 tc (RBdHoareDeno r)
    (bdhoare_deno_subgoals (FApi.tc1_hyps tc) concl r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareDeno n ->
         Some (EcPlRecheck.checker_of "bdhoare-deno" (fun _ concl -> concl)
                 (fun hyps concl -> bdhoare_deno_subgoals hyps concl n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): an equality with the probability on its
   right-hand side is first turned around. *)
let t_bdhoare_deno_full (r : bdhoare_deno) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | Fapp ({f_node = Fop (op, _)}, [f; _bd])
      when EcPath.p_equal op EcCoreLib.CI_Bool.p_eq && not (is_pr f) ->
    FApi.t_seq t_symmetry (t_bdhoare_deno r) tc

  | _ -> t_bdhoare_deno r tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the judgement is given by a proof term, or cut from the
   goal (precondition [true] and postcondition the event by default),
   then the derived rule is applied and the premise closed with it. *)
let process_bdhoare_deno (info : deno_ppterm) (tc : tcenv1) =
  let error () =
    tc_error !!tc "the conclusion is not a suitable Pr expression" in

  let process_cut (pre, post) =
    let hyps, concl = FApi.tc1_flat tc in
    let cmp, f, bd =
      match concl.f_node with
      | Fapp ({f_node = Fop (op, _)}, [f1; f2])
          when EcPath.p_equal op EcCoreLib.CI_Bool.p_eq
        ->
             if is_pr f1 then (FHeq, f1, f2)
        else if is_pr f2 then (FHeq, f2, f1)
        else error ()

      | Fapp({f_node = Fop (op, _)}, [f1; f2])
          when EcPath.p_equal op EcCoreLib.CI_Real.p_real_le
        ->
             if is_pr f1 then (FHle, f1, f2) (* f1 <= f2 *)
        else if is_pr f2 then (FHge, f2, f1) (* f2 >= f1 *)
        else error ()

      | _ -> error ()
    in

    let { pr_fun = f } as pr = destr_pr f in
    let event = pr.pr_event in
    let m = event.m in
    let penv, qenv = LDecl.hoareF m f hyps in
    let pre  = pre  |> omap_dfl (fun p -> TTC.pf_process_formula !!tc penv p) f_true in
    let post = post |> omap_dfl (fun p -> TTC.pf_process_formula !!tc qenv p) event.inv in

    f_bdHoareF { m; inv = pre; } f { m; inv = post; } cmp { m; inv = bd; }
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:process_cut tc info in

  let bhf = pf_as_bdhoareF !!tc ax in

  FApi.t_first
    (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt)
    (t_bdhoare_deno_full { bdd_pre = bhf_pr bhf; bdd_post = bhf_po bhf; } tc)
