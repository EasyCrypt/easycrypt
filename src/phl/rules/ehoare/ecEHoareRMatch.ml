(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameters of the framed ehoare [rmatch] rule, resolved: the position of
   the match and its constructor are integer indices. Nothing to resolve:
   the same record is the rule argument and the node payload. *)
type ehoare_rmatch_framed = {
  ehrmf_at   : EcMatching.Position.nm_codepos1;   (* position of the match *)
  ehrmf_ctor : int;                                (* index of the constructor *)
}

type EcCoreGoal.rule += REHoareRMatchFramed of ehoare_rmatch_framed

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   instruction is a [match] with that constructor, the framing condition,
   the form [P `|` f] of the precondition) are re-checked here, from the
   goal: the checker re-validates them. The prefix obligation is a hoare
   judgement on [P], and [e = C ys] is added to [P]. *)
let ehoare_rmatch_framed_subgoals
    (hyps : LDecl.hyps) (hs : eHoareS) (n : ehoare_rmatch_framed)
=
  let env = LDecl.toenv hyps in
  let r = EcPlRCond.rmatch_select env hs.ehs_m n.ehrmf_at n.ehrmf_ctor hs.ehs_s in
  if not (EcPlRCond.rmatch_can_frame env ~can_frame:true n.ehrmf_at hs.ehs_s) then
    raise (InvalidTransform "the framed form of match does not apply");
  let p, f =
    match destr_app (ehs_pr hs).inv with
    | o, [p; f] when f_equal o fop_interp_ehoare_form -> p, f
    | _ -> raise (InvalidTransform "the pre should have the form \"_ `|` _\"") in
  let p  = { m = (ehs_pr hs).m; inv = p; } in
  let pr = map_ss_inv1 (fun p -> f_interp_ehoare_form p f) (map_ss_inv2 f_and r.rm_eq p) in
  let a = f_hoareS (snd hs.ehs_m) p r.rm_hd (POE.lift r.rm_post) in
  let b = f_eHoareS (snd r.rm_me) pr r.rm_framed (ehs_po hs) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). A side condition that does not hold is reported as a tactic
   error. *)
let t_ehoare_rmatch_framed (n : ehoare_rmatch_framed) (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  let sg =
    try  ehoare_rmatch_framed_subgoals (FApi.tc1_hyps tc) hs n
    with InvalidTransform msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REHoareRMatchFramed n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareRMatchFramed n ->
         Some (EcPlRecheck.checker_of "ehoare-rmatch-framed" pf_as_ehoareS
                 (fun hyps hs -> ehoare_rmatch_framed_subgoals hyps hs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Parameters of the ehoare [rmatch] tactic as supplied by the caller: high
   level, the position and the constructor are still symbolic. *)
type ehoare_rmatch_rule = {
  ehrmr_at   : EcMatching.Position.codepos1;   (* position of the match *)
  ehrmr_ctor : EcSymbols.symbol;               (* constructor of the branch *)
}

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): resolve the position and the constructor
   (failing as before the migration), then apply the framed rule when the
   framing condition holds, the [rmatch] transformation through the ehoare
   transformation rule otherwise (both check the form of the
   precondition). *)
let t_ehoare_rmatch (r : ehoare_rmatch_rule) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hs  = tc1_as_ehoareS tc in
  let at, j = EcPlRCond.resolve_rmatch !!tc env r.ehrmr_at r.ehrmr_ctor hs.ehs_s in
  if EcPlRCond.rmatch_can_frame env ~can_frame:true at hs.ehs_s then
    t_ehoare_rmatch_framed { ehrmf_at = at; ehrmf_ctor = j } tc
  else
    let tr = EcTrRMatch.TrRMatch { trrm_at = at; trrm_ctor = j } in
    EcEHoareTransform.t_ehoare_transform { ehtr_tr = tr } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [eHoareS]. Type the position in
   its memory, then apply the tactic. *)
let process_ehoare_rmatch
    (c : EcSymbols.symbol) (at : EcParsetree.pcodepos1) (tc : tcenv1)
=
  let at = tc1_process_codepos1 tc (None, at) in
  t_ehoare_rmatch { ehrmr_at = at; ehrmr_ctor = c } tc
