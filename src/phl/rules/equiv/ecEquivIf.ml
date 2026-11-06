(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcAst
open EcModules

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* The two-sided equiv [if] rule has no parameters: the statements are the
   conditionals. The one-sided rule is parameterized by its side, nothing
   to resolve: the same record is the rule argument and the node
   payload. *)
type equiv_if_onesided = {
  eio_side : side;
}

type EcCoreGoal.rule +=
  | REquivIf
  | REquivIfOneSided of equiv_if_onesided

(* -------------------------------------------------------------------- *)
(* The statement [s], a single conditional. *)
let single_if (who : string) (s : stmt) =
  match s.s_node with
  | [{ i_node = Sif (e, c1, c2) }] -> (e, c1, c2)
  | _ -> failwith (who ^ ": the statement is not a single conditional")

(* The condition [b] of the conditional of side [side], as a relation. *)
let side_cond (es : equivS) (side : side) (e : expr) : ts_inv =
  let ml, mr = fst es.es_ml, fst es.es_mr in
  match side with
  | `Left  -> ss_inv_generalize_right (ss_inv_of_expr ml e) mr
  | `Right -> ss_inv_generalize_left  (ss_inv_of_expr mr e) ml

(* -------------------------------------------------------------------- *)
(* Pure cores shared by the rules and their checkers. Their side
   conditions (the statements are single conditionals) are part of them,
   so the checkers re-validate them. *)
let equiv_if_subgoals (es : equivS) : form list =
  let el, cl1, cl2 = single_if "equiv-if" es.es_sl in
  let er, cr1, cr2 = single_if "equiv-if" es.es_sr in
  let bl = side_cond es `Left  el in
  let br = side_cond es `Right er in
  let fiff =
    EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr
      (map_ts_inv2 f_imp (es_pr es) (map_ts_inv2 f_iff bl br)) in
  let concl b sl sr =
    f_equivS (snd es.es_ml) (snd es.es_mr)
      (map_ts_inv2 f_and (es_pr es) b) sl sr (es_po es) in
  [fiff; concl bl cl1 cr1; concl (map_ts_inv1 f_not bl) cl2 cr2]

let equiv_if_onesided_subgoals (es : equivS) (n : equiv_if_onesided) =
  let side = n.eio_side in
  let e, c1, c2 =
    single_if "equiv-if-onesided" (sideif side es.es_sl es.es_sr) in
  let b = side_cond es side e in
  let concl b s =
    let sl, sr = sideif side (s, es.es_sr) (es.es_sl, s) in
    f_equivS (snd es.es_ml) (snd es.es_mr)
      (map_ts_inv2 f_and (es_pr es) b) sl sr (es_po es) in
  [concl b c1; concl (map_ts_inv1 f_not b) c2]

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_equiv_if (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_if_subgoals es
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc REquivIf sg

let t_equiv_if_onesided (r : equiv_if_onesided) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_if_onesided_subgoals es r
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REquivIfOneSided r) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivIf ->
         Some (EcPlRecheck.checker_of "equiv-if" pf_as_equivS
                 (fun _hyps es -> equiv_if_subgoals es))
     | REquivIfOneSided n ->
         Some (EcPlRecheck.checker_of "equiv-if-onesided" pf_as_equivS
                 (fun _hyps es -> equiv_if_onesided_subgoals es n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): push the continuation of the conditional of
   side [side] into its branches, when not empty. *)
let t_equiv_if_push (side : side) (c : stmt) =
  if List.is_empty c.s_node then t_id else
    EcEquivTransform.t_equiv_transform
      { etr_side = side; etr_tr = EcTrIfPush.TrIfPush }

(* Derived (no proof-node): on [if b then c1 else c2; c] (on one side, or
   on both sides), push the continuations into the branches, then apply
   the one-sided (resp. two-sided) rule. *)
let t_equiv_if_head (side : oside) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  match side with
  | Some side ->
      let _, c = tc1_first_if tc (sideif side es.es_sl es.es_sr) in
      FApi.t_seq
        (t_equiv_if_push side c)
        (t_equiv_if_onesided { eio_side = side }) tc

  | None ->
      let _, cl = tc1_first_if tc es.es_sl in
      let _, cr = tc1_first_if tc es.es_sr in
      FApi.t_seqs
        [t_equiv_if_push `Left cl; t_equiv_if_push `Right cr; t_equiv_if] tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS]. *)
let process_equiv_if (info : pcond_info) (tc : tcenv1) =
  (* By default, split before the last top-level conditional. *)
  let default_if (i : EcMatching.Position.codegap1 option) s =
    ofdfl (fun _ ->
        EcMatching.Position.(GapBefore (cpos1 (tc1_pos_last_if tc s)))) i in

  match info with
  | `Head side -> t_equiv_if_head side tc

  | `Seq (side, (i1, i2), f) ->
    let es = tc1_as_equivS tc in
    let f  = TTC.tc1_process_prhl_formula tc f in
    let i1 = Option.map (fun i1 -> tc1_process_codegap1 tc (side, i1)) i1 in
    let i2 = Option.map (fun i2 -> tc1_process_codegap1 tc (side, i2)) i2 in
    let n1 = default_if i1 es.es_sl in
    let n2 = default_if i2 es.es_sr in
    FApi.t_seqsub
      (EcEquivSeq.t_equiv_seq { esr_at = (n1, n2); esr_mid = f })
      [t_id; t_equiv_if_head side] tc

  | `SeqOne (s, i, f1, f2) ->
    let es = tc1_as_equivS tc in
    let i  = Option.map (fun i -> tc1_process_codegap1 tc (Some s, i)) i in
    let n  = default_if i (sideif s es.es_sl es.es_sr) in
    let _, f1 = TTC.tc1_process_Xhl_formula ~side:s tc f1 in
    let _, f2 = TTC.tc1_process_Xhl_formula ~side:s tc f2 in
    FApi.t_seqsub
      (EcEquivSeq.t_equiv_seq_onesided s n f1 f2)
      [t_id; EcBdHoareIf.t_bdhoare_if_head] tc
