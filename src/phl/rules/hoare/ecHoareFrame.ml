(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the hoare frame rules: the new postcondition [Q'] (normal
   and exceptional parts). Already typed, nothing to resolve: the same record
   is the rule argument and the node payload. *)
type hoare_frame = {
  hfr_post : hs_inv;
}

type EcCoreGoal.rule +=
  | RHoareSFrame of hoare_frame
  | RHoareFFrame of hoare_frame

(* -------------------------------------------------------------------- *)
(* The postcondition condition, before framing:
     (Q' => Q) /\ (for each exception e, Q'_e => Q_e) *)
let hoare_frame_post_cond (post : exnpost) (fpost : exnpost) : form =
  let post , epost  = POE.destruct post  in
  let fpost, fepost = POE.destruct fpost in
  let cond   = f_imp post fpost in
  let econd1 = TTC.merge2_poe_list fepost epost in
  List.fold f_and cond econd1

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. *)
let hoareS_frame_subgoals (hyps : LDecl.hyps) (hs : sHoareS) (n : hoare_frame) =
  let env  = LDecl.toenv hyps in
  let p    = hs_inv_rebind n.hfr_post (fst hs.hs_m) in
  let cond = hoare_frame_post_cond p.hsi_inv (hs_po hs).hsi_inv in
  let cond1, _, _ =
    EcPlFrame.ss_frame_cond_S ~mk_other:false
      env hs.hs_s hs.hs_m (hs_pr hs) { m = fst hs.hs_m; inv = cond } in
  let cond2 = f_hoareS (snd hs.hs_m) (hs_pr hs) hs.hs_s p in
  [cond1; cond2]

let hoareF_frame_subgoals (hyps : LDecl.hyps) (hf : sHoareF) (n : hoare_frame) =
  let env  = LDecl.toenv hyps in
  let p    = hs_inv_rebind n.hfr_post hf.hf_m in
  let cond = hoare_frame_post_cond p.hsi_inv (hf_po hf).hsi_inv in
  let cond1, _, _ =
    EcPlFrame.ss_frame_cond_F ~mk_other:false
      env hyps hf.hf_f hf.hf_m (hf_pr hf) { m = hf.hf_m; inv = cond } in
  let cond2 = f_hoareF (hf_pr hf) hf.hf_f p in
  [cond1; cond2]

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_hoareS_frame (r : hoare_frame) (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  FApi.xrule1 tc (RHoareSFrame r)
    (hoareS_frame_subgoals (FApi.tc1_hyps tc) hs r)

let t_hoareF_frame (r : hoare_frame) (tc : tcenv1) =
  let hf = tc1_as_hoareF tc in
  FApi.xrule1 tc (RHoareFFrame r)
    (hoareF_frame_subgoals (FApi.tc1_hyps tc) hf r)

(* -------------------------------------------------------------------- *)
(* Checkers: rerun the core, which recomputes the variables written by the
   program — the soundness-critical part of framing — from the goal's own
   context. *)
let () =
  register_rule_checker
    (function
     | RHoareSFrame n ->
         Some (EcPlRecheck.checker_of "hoareS-frame" pf_as_hoareS
                 (fun hyps hs -> hoareS_frame_subgoals hyps hs n))
     | RHoareFFrame n ->
         Some (EcPlRecheck.checker_of "hoareF-frame" pf_as_hoareF
                 (fun hyps hf -> hoareF_frame_subgoals hyps hf n))
     | _ -> None)
