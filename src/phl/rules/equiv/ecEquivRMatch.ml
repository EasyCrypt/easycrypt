(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowPhlGoal
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameters of the framed (one-sided) equiv [rmatch] rule, resolved: the
   position of the match and its constructor are integer indices. Nothing
   to resolve: the same record is the rule argument and the node
   payload. *)
type equiv_rmatch_framed = {
  ermf_side : side;                               (* side of the match *)
  ermf_at   : EcMatching.Position.nm_codepos1;   (* position of the match *)
  ermf_ctor : int;                                (* index of the constructor *)
}

type EcCoreGoal.rule += REquivRMatchFramed of equiv_rmatch_framed

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   instruction is a [match] with that constructor, the prefix is empty)
   are re-checked here, from the goal: the checker re-validates them. The
   prefix obligation is a hoare judgement on the side of the match, the
   other memory being universally quantified, and [e = C ys] is added to
   the relational precondition. *)
let equiv_rmatch_framed_subgoals
    (hyps : LDecl.hyps) (es : equivS) (n : equiv_rmatch_framed)
=
  let env  = LDecl.toenv hyps in
  let side = n.ermf_side in
  let m, mo, s =
    match side with
    | `Left  -> es.es_ml, es.es_mr, es.es_sl
    | `Right -> es.es_mr, es.es_ml, es.es_sr in
  let r = EcPlRCond.rmatch_select env m n.ermf_at n.ermf_ctor s in
  if not (EcPlRCond.rmatch_can_frame env ~can_frame:false n.ermf_at s) then
    raise (InvalidTransform "the framed form of match does not apply");
  let ss_inv_generalize_other inv =
    sideif side ss_inv_generalize_right ss_inv_generalize_left inv (fst mo) in
  let ts_inv_lower_side1 =
    sideif side ts_inv_lower_left1 ts_inv_lower_right1 in
  let eq = ss_inv_generalize_other (ss_inv_rebind r.rm_eq (fst m)) in
  let po = POE.lift r.rm_post in
  let a =
    f_forall_mems_ss_inv mo
      (ts_inv_lower_side1 (fun pr -> f_hoareS (snd m) pr r.rm_hd po) (es_pr es)) in
  let b =
    let pr = map_ts_inv2 f_and eq (es_pr es) in
    match side with
    | `Left  ->
        f_equivS (snd r.rm_me) (snd es.es_mr) pr r.rm_framed es.es_sr (es_po es)
    | `Right ->
        f_equivS (snd es.es_ml) (snd r.rm_me) pr es.es_sl r.rm_framed (es_po es) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). A side condition that does not hold is reported as a tactic
   error. *)
let t_equiv_rmatch_framed (n : equiv_rmatch_framed) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_rmatch_framed_subgoals (FApi.tc1_hyps tc) es n
    with InvalidTransform msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REquivRMatchFramed n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivRMatchFramed n ->
         Some (EcPlRecheck.checker_of "equiv-rmatch-framed" pf_as_equivS
                 (fun hyps es -> equiv_rmatch_framed_subgoals hyps es n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Parameters of the (one-sided) equiv [rmatch] tactic as supplied by the
   caller: high level, the position and the constructor are still
   symbolic. *)
type equiv_rmatch_rule = {
  ermr_side : side;                            (* side of the match *)
  ermr_at   : EcMatching.Position.codepos1;   (* position of the match *)
  ermr_ctor : EcSymbols.symbol;               (* constructor of the branch *)
}

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): resolve the position and the constructor on the
   chosen side (failing as before the migration), then apply the framed
   rule when the prefix is empty, the [rmatch] transformation to that side
   through the equiv transformation rule otherwise. *)
let t_equiv_rmatch (r : equiv_rmatch_rule) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_equivS tc in
  let s   = sideif r.ermr_side es.es_sl es.es_sr in
  let at, j = EcPlRCond.resolve_rmatch !!tc env r.ermr_at r.ermr_ctor s in
  if EcPlRCond.rmatch_can_frame env ~can_frame:false at s then
    t_equiv_rmatch_framed { ermf_side = r.ermr_side; ermf_at = at; ermf_ctor = j } tc
  else
    let tr = EcTrRMatch.TrRMatch { trrm_at = at; trrm_ctor = j } in
    EcEquivTransform.t_equiv_transform { etr_side = r.ermr_side; etr_tr = tr } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS] (or is reported as not
   being one when typing the position). Type the position in the memory of
   [side], then apply the tactic. *)
let process_equiv_rmatch
    (side : side) (c : EcSymbols.symbol) (at : pcodepos1) (tc : tcenv1)
=
  let at = tc1_process_codepos1 tc (Some side, at) in
  t_equiv_rmatch { ermr_side = side; ermr_at = at; ermr_ctor = c } tc
