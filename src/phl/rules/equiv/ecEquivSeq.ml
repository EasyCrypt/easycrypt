(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcAst
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the equiv [seq] rule as supplied by the caller: high level,
   the split positions (left, right) are still symbolic code gaps. *)
type equiv_seq_rule = {
  esr_at  : EcMatching.Position.codegap1 pair;   (* split positions *)
  esr_mid : ts_inv;                               (* intermediate relation *)
}

(* Low-level parameters recorded in the proof-node: the split positions are
   the RESOLVED integer indices. *)
type equiv_seq_node = {
  esn_at  : EcMatching.Position.nm_codegap1 pair;   (* resolved split indices *)
  esn_mid : ts_inv;                                  (* intermediate relation *)
}

type EcCoreGoal.rule += REquivSeq of equiv_seq_node

(* -------------------------------------------------------------------- *)
(* Pure low-level core shared by the rule and its checker: split both
   statements at the already-resolved indices and build the pre/mid and
   mid/post subgoals. Needs no environment. *)
let equiv_seq_subgoals (es : equivS) (n : equiv_seq_node) : form list =
  let il, ir   = n.esn_at in
  let sl1, sl2 = EcMatching.Position.split_at_nmcgap1 il es.es_sl in
  let sr1, sr2 = EcMatching.Position.split_at_nmcgap1 ir es.es_sr in
  let mtl, mtr = snd es.es_ml, snd es.es_mr in
  let a = f_equivS mtl mtr (es_pr es) (stmt sl1) (stmt sr1) n.esn_mid in
  let b = f_equivS mtl mtr n.esn_mid (stmt sl2) (stmt sr2) (es_po es) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB): resolve both code gaps to indices (the env-dependent step),
   record the resolved node, and build its subgoals through the shared core.
   The legacy positional interface (EcPhlSeq.t_equiv_seq) adapts onto it. *)
let t_equiv_seq (r : equiv_seq_rule) tc =
  let env    = FApi.tc1_env tc in
  let es     = tc1_as_equivS tc in
  let gl, gr = r.esr_at in
  let n = { esn_at  = (s_split_index env gl es.es_sl,
                       s_split_index env gr es.es_sr);
            esn_mid = r.esr_mid; } in
  FApi.xrule1 tc (REquivSeq n) (equiv_seq_subgoals es n)

(* -------------------------------------------------------------------- *)
(* Checker: rerun ONLY the low-level core on the recorded indices (see
   [EcPhlRecheck]). *)
let () =
  register_rule_checker
    (function
     | REquivSeq n ->
         Some (EcPhlRecheck.checker_of "equiv-seq" pf_as_equivS
                 (fun _hyps es -> equiv_seq_subgoals es n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* One-sided [seq] (derived, no proof-node): split one side only, at [i],
   with the one-sided intermediate assertions [pre] / [post]. Expands to the
   two-sided rule (the other side split at its end) followed by [conseq]
   steps that discharge the one-sided part.

   TEMPORARY: depends on the not-yet-migrated [EcPhlConseq]. *)
let t_equiv_seq_onesided side i pre post tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let (ml, mr) = fst es.es_ml, fst es.es_mr in
  let s, p', q' =
    match side with
    | `Left  ->
      let p' = ss_inv_generalize_as_left pre ml mr in
      let q' = ss_inv_generalize_as_left post ml mr in
      es.es_sl, p', q'
    | `Right ->
      let p' = ss_inv_generalize_as_right pre ml mr in
      let q' = ss_inv_generalize_as_right post ml mr in
      es.es_sr, p', q'
  in
  let generalize_mod_side = sideif side generalize_mod_left generalize_mod_right in
  let ij =
    match side with
    | `Left  -> (i, EcMatching.Position.codegap1_end)
    | `Right -> (EcMatching.Position.codegap1_end, i) in
  let _s1, s2 = s_split env i s in

  let modi = EcPV.s_write env (EcModules.stmt s2) in
  let r = map_ts_inv2 f_and p' (generalize_mod_side env modi (map_ts_inv2 f_imp q' (es_po es))) in
  FApi.t_seqsub (t_equiv_seq { esr_at = ij; esr_mid = r })
    [t_id; (* s1 ~ s' : pr ==> r *)
     FApi.t_seqsub (EcPhlConseq.t_equivS_conseq_nm p' q')
       [(* r => forall mod, post => post' *) t_trivial;
        (* r => p' *) t_trivial;
        (* s1 ~ [] : p' ==> q' *) EcPhlConseq.t_equivS_conseq_bd side pre post
       ]
    ] tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS]. A single position is the
   one-sided form (side required, pre and post assertions); a pair of
   positions is the two-sided form (no side, single relation). *)
let process_equiv_seq (info : seq_info) tc =
  begin match info.seqi_bd with
  | PSeqNone -> ()
  | _        -> tc_error !!tc "optional bound parameter not supported" end;

  match info.seqi_at with
  | Single i ->
      let side =
        match info.seqi_side with
        | None      -> tc_error !!tc "seq onsided: side information expected"
        | Some side -> side in
      let pre, post =
        match info.seqi_mid with
        | Single _ -> tc_error !!tc "seq onsided: a pre and a post is expected"
        | Double (pre, post) ->
          let _, pre  = TTC.tc1_process_Xhl_formula ~side tc pre in
          let _, post = TTC.tc1_process_Xhl_formula ~side tc post in
          (pre, post) in
      let i = EcLowPhlGoal.tc1_process_codegap1 tc (Some side, i) in
      t_equiv_seq_onesided side i pre post tc

  | Double (i, j) ->
      if is_some info.seqi_side then
        tc_error !!tc "seq: no side information expected";
      let phi =
        match info.seqi_mid with
        | Single phi -> phi
        | Double _   -> tc_error !!tc "seq: a single formula is expected" in
      let phi = TTC.tc1_process_prhl_formula tc phi in
      (* NB: both positions are typed in the left memory, as before the
         migration (behaviour preserved; the right one should probably use
         the right memory). *)
      let i = EcLowPhlGoal.tc1_process_codegap1 tc (Some `Left, i) in
      let j = EcLowPhlGoal.tc1_process_codegap1 tc (Some `Left, j) in
      t_equiv_seq { esr_at = (i, j); esr_mid = phi } tc
