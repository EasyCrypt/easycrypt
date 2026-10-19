(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare frame rules: the new postcondition [Q']. Already
   typed, nothing to resolve: the same record is the rule argument and the
   node payload. *)
type bdhoare_frame = {
  bfr_post : ss_inv;
}

type EcCoreGoal.rule +=
  | RBdHoareSFrame of bdhoare_frame
  | RBdHoareFFrame of bdhoare_frame

(* -------------------------------------------------------------------- *)
(* The postcondition condition, before framing. Its direction follows the
   comparison: an upper bound needs [Q] to imply [Q'], a lower bound the
   converse, an equality both. *)
let bdhoare_frame_post_cond (cmp : hoarecmp) (q : ss_inv) (q' : ss_inv) =
  match cmp with
  | FHle -> map_ss_inv2 f_imp q  q'
  | FHeq -> map_ss_inv2 f_iff q  q'
  | FHge -> map_ss_inv2 f_imp q' q

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. *)
let bdhoareS_frame_subgoals
    (hyps : LDecl.hyps) (hs : bdHoareS) (n : bdhoare_frame)
=
  let env  = LDecl.toenv hyps in
  let post = ss_inv_rebind n.bfr_post (fst hs.bhs_m) in
  let cond = bdhoare_frame_post_cond hs.bhs_cmp (bhs_po hs) post in
  let cond1, _, _ =
    EcPlFrame.ss_frame_cond_S ~mk_other:false
      env hs.bhs_s hs.bhs_m (bhs_pr hs) cond in
  let cond2 =
    f_bdHoareS (snd hs.bhs_m) (bhs_pr hs) hs.bhs_s post hs.bhs_cmp (bhs_bd hs) in
  [cond1; cond2]

let bdhoareF_frame_subgoals
    (hyps : LDecl.hyps) (hf : bdHoareF) (n : bdhoare_frame)
=
  let env  = LDecl.toenv hyps in
  let post = ss_inv_rebind n.bfr_post hf.bhf_m in
  let cond = bdhoare_frame_post_cond hf.bhf_cmp (bhf_po hf) post in
  let cond1, _, _ =
    EcPlFrame.ss_frame_cond_F ~mk_other:false
      env hyps hf.bhf_f hf.bhf_m (bhf_pr hf) cond in
  let cond2 = f_bdHoareF (bhf_pr hf) hf.bhf_f post hf.bhf_cmp (bhf_bd hf) in
  [cond1; cond2]

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_bdhoareS_frame (r : bdhoare_frame) (tc : tcenv1) =
  let hs = tc1_as_bdhoareS tc in
  FApi.xrule1 tc (RBdHoareSFrame r)
    (bdhoareS_frame_subgoals (FApi.tc1_hyps tc) hs r)

let t_bdhoareF_frame (r : bdhoare_frame) (tc : tcenv1) =
  let hf = tc1_as_bdhoareF tc in
  FApi.xrule1 tc (RBdHoareFFrame r)
    (bdhoareF_frame_subgoals (FApi.tc1_hyps tc) hf r)

(* -------------------------------------------------------------------- *)
(* Checkers: rerun the core, which recomputes the variables written by the
   program from the goal's own context. *)
let () =
  register_rule_checker
    (function
     | RBdHoareSFrame n ->
         Some (EcPlRecheck.checker_of "bdhoareS-frame" pf_as_bdhoareS
                 (fun hyps hs -> bdhoareS_frame_subgoals hyps hs n))
     | RBdHoareFFrame n ->
         Some (EcPlRecheck.checker_of "bdhoareF-frame" pf_as_bdhoareF
                 (fun hyps hf -> bdhoareF_frame_subgoals hyps hf n))
     | _ -> None)
