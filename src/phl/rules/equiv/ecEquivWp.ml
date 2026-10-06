(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcEnv

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameter of the equiv [wp] rule: whether the weakest precondition
   let-binds its substitutions. Nothing to resolve: the same record is the
   rule argument and the node payload. *)
type equiv_wp = {
  ewp_uselet : bool;
}

type EcCoreGoal.rule += REquivWp of equiv_wp

(* -------------------------------------------------------------------- *)
(* The two-sided wp: the wp of the left statement, then that of the right
   one. Returns the instructions that could not be traversed on each side. *)
let equiv_wp ~uselet (hyps : LDecl.hyps) (es : equivS) sl sr =
  let mc = (fst es.es_ml, fst es.es_mr) in
  let rl, post = EcPlWp.wp ~mc ~uselet hyps es.es_ml sl (POE.empty (es_po es).inv) in
  let rr, post = EcPlWp.wp ~mc ~uselet hyps es.es_mr sr (POE.empty post) in
  (rl, rr, post)

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. The rule has no premise;
   its side conditions (both statements are entirely wp-able, the
   precondition is their weakest precondition) are part of it, so the
   checker re-validates them. *)
let equiv_wp_subgoals (hyps : LDecl.hyps) (es : equivS) (n : equiv_wp) =
  let rl, rr, pre = equiv_wp ~uselet:n.ewp_uselet hyps es es.es_sl es.es_sr in
  if not (List.is_empty rl) then
    failwith "equiv-wp: the left statement is not wp-able";
  if not (List.is_empty rr) then
    failwith "equiv-wp: the right statement is not wp-able";
  if not (EcReduction.is_conv hyps (es_pr es).inv pre) then
    failwith "equiv-wp: the precondition is not the weakest precondition";
  []

(* -------------------------------------------------------------------- *)
(* Rule (TCB). Its failures are reported as tactic errors. *)
let t_equiv_wp (r : equiv_wp) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let es   = tc1_as_equivS tc in
  let subgoals =
    try  equiv_wp_subgoals hyps es r
    with Failure msg -> tc_error !!tc ~who:"wp" "%s" msg in
  FApi.xrule1 tc (REquivWp r) subgoals

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivWp n ->
         Some (EcPlRecheck.checker_of "equiv-wp" pf_as_equivS
                 (fun hyps es -> equiv_wp_subgoals hyps es n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): the surface [wp]. Compute the two-sided wp of
   the suffixes after [(i, j)] (of the longest wp-able suffixes when no
   positions are given), split there with [seq], using it as intermediate
   relation, and close the suffix premise with the rule. *)
let t_equiv_wp_full
  ?(uselet = true) (ij : EcMatching.Position.codegap1 pair option) tc
=
  let hyps = FApi.tc1_hyps tc in
  let env  = LDecl.toenv hyps in
  let es   = tc1_as_equivS tc in
  let i = omap fst ij and j = omap snd ij in
  let s_hdl, s_wpl = o_split env i es.es_sl in
  let s_hdr, s_wpr = o_split env j es.es_sr in
  let rl, rr, pre =
    equiv_wp ~uselet hyps es (EcModules.stmt s_wpl) (EcModules.stmt s_wpr) in
  EcPlWp.check_wp_progress tc i rl;
  EcPlWp.check_wp_progress tc j rr;
  let at k = EcMatching.Position.(GapBefore (cpos1 k)) in
  let atl  = at (List.length s_hdl + List.length rl) in
  let atr  = at (List.length s_hdr + List.length rr) in
  let mid  = { ml = fst es.es_ml; mr = fst es.es_mr; inv = pre; } in
  FApi.t_seqsub
    (EcEquivSeq.t_equiv_seq { esr_at = (atl, atr); esr_mid = mid })
    [t_id; t_equiv_wp { ewp_uselet = uselet }]
    tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS]. No position or a pair
   of them; positions are typed in the ambient environment. *)
let process_equiv_wp (cpos : EcParsetree.pdocodegap1) tc =
  let cpos = omap (EcTyping.trans_dcodegap1 (FApi.tc1_env tc)) cpos in
  match cpos with
  | None                 -> t_equiv_wp_full None tc
  | Some (Double (i, j)) -> t_equiv_wp_full (Some (i, j)) tc
  | Some (Single _)      ->
      tc_error_noXhl ~kinds:[`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt] !!tc
