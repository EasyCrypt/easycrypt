(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameters of the framed hoare [rmatch] rule, resolved: the position of
   the match and its constructor are integer indices. Nothing to resolve:
   the same record is the rule argument and the node payload. *)
type hoare_rmatch_framed = {
  hrmf_at   : EcMatching.Position.nm_codepos1;   (* position of the match *)
  hrmf_ctor : int;                                (* index of the constructor *)
}

type EcCoreGoal.rule += RHoareRMatchFramed of hoare_rmatch_framed

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   instruction is a [match] with that constructor, the framing condition)
   are re-checked here, from the goal: the checker re-validates them. *)
let hoare_rmatch_framed_subgoals
    (hyps : LDecl.hyps) (hs : sHoareS) (n : hoare_rmatch_framed)
=
  let env = LDecl.toenv hyps in
  let r = EcPlRCond.rmatch_select env hs.hs_m n.hrmf_at n.hrmf_ctor hs.hs_s in
  if not (EcPlRCond.rmatch_can_frame env ~can_frame:true n.hrmf_at hs.hs_s) then
    raise (InvalidTransform "the framed form of match does not apply");
  let a = f_hoareS (snd hs.hs_m) (hs_pr hs) r.rm_hd
            (update_hs_ss r.rm_post (hs_po hs)) in
  let b = f_hoareS (snd r.rm_me) (map_ss_inv2 f_and r.rm_eq (hs_pr hs))
            r.rm_framed (hs_po hs) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). A side condition that does not hold is reported as a tactic
   error. *)
let t_hoare_rmatch_framed (n : hoare_rmatch_framed) (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let sg =
    try  hoare_rmatch_framed_subgoals (FApi.tc1_hyps tc) hs n
    with InvalidTransform msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (RHoareRMatchFramed n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareRMatchFramed n ->
         Some (EcPlRecheck.checker_of "hoare-rmatch-framed" pf_as_hoareS
                 (fun hyps hs -> hoare_rmatch_framed_subgoals hyps hs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Parameters of the hoare [rmatch] tactic as supplied by the caller: high
   level, the position and the constructor are still symbolic. *)
type hoare_rmatch_rule = {
  hrmr_at   : EcMatching.Position.codepos1;   (* position of the match *)
  hrmr_ctor : EcSymbols.symbol;               (* constructor of the branch *)
}

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): resolve the position and the constructor
   (failing as before the migration), then apply the framed rule when the
   framing condition holds, the [rmatch] transformation through the hoare
   transformation rule otherwise. *)
let t_hoare_rmatch (r : hoare_rmatch_rule) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hs  = tc1_as_hoareS tc in
  let at, j = EcPlRCond.resolve_rmatch !!tc env r.hrmr_at r.hrmr_ctor hs.hs_s in
  if EcPlRCond.rmatch_can_frame env ~can_frame:true at hs.hs_s then
    t_hoare_rmatch_framed { hrmf_at = at; hrmf_ctor = j } tc
  else
    let tr = EcTrRMatch.TrRMatch { trrm_at = at; trrm_ctor = j } in
    EcHoareTransform.t_hoare_transform { htr_tr = tr } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS] (or is reported as not
   being one when typing the position). Type the position in its memory,
   then apply the tactic. *)
let process_hoare_rmatch
    (c : EcSymbols.symbol) (at : EcParsetree.pcodepos1) (tc : tcenv1)
=
  let at = tc1_process_codepos1 tc (None, at) in
  t_hoare_rmatch { hrmr_at = at; hrmr_ctor = c } tc
