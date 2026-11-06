(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameters of the framed bdhoare [rmatch] rule, resolved: the position
   of the match and its constructor are integer indices. Nothing to
   resolve: the same record is the rule argument and the node payload. *)
type bdhoare_rmatch_framed = {
  brmf_at   : EcMatching.Position.nm_codepos1;   (* position of the match *)
  brmf_ctor : int;                                (* index of the constructor *)
}

type EcCoreGoal.rule += RBdHoareRMatchFramed of bdhoare_rmatch_framed

(* -------------------------------------------------------------------- *)
(* The framed form ignores the initial memories in which the prefix does
   not terminate: sound for an upper bound only, unless the prefix is
   empty. *)
let can_frame (bhs : bdHoareS) = bhs.bhs_cmp = FHle

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   instruction is a [match] with that constructor, the framing condition)
   are re-checked here, from the goal: the checker re-validates them. *)
let bdhoare_rmatch_framed_subgoals
    (hyps : LDecl.hyps) (bhs : bdHoareS) (n : bdhoare_rmatch_framed)
=
  let env = LDecl.toenv hyps in
  let r = EcPlRCond.rmatch_select env bhs.bhs_m n.brmf_at n.brmf_ctor bhs.bhs_s in
  if not (EcPlRCond.rmatch_can_frame env ~can_frame:(can_frame bhs) n.brmf_at bhs.bhs_s) then
    raise (InvalidTransform "the framed form of match does not apply");
  let a = f_hoareS (snd bhs.bhs_m) (bhs_pr bhs) r.rm_hd (POE.lift r.rm_post) in
  let b = f_bdHoareS (snd r.rm_me) (map_ss_inv2 f_and r.rm_eq (bhs_pr bhs))
            r.rm_framed (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). A side condition that does not hold is reported as a tactic
   error. *)
let t_bdhoare_rmatch_framed (n : bdhoare_rmatch_framed) (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  let sg  =
    try  bdhoare_rmatch_framed_subgoals (FApi.tc1_hyps tc) bhs n
    with InvalidTransform msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (RBdHoareRMatchFramed n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareRMatchFramed n ->
         Some (EcPlRecheck.checker_of "bdhoare-rmatch-framed" pf_as_bdhoareS
                 (fun hyps bhs -> bdhoare_rmatch_framed_subgoals hyps bhs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare [rmatch] tactic as supplied by the caller:
   high level, the position and the constructor are still symbolic. *)
type bdhoare_rmatch_rule = {
  brmr_at   : EcMatching.Position.codepos1;   (* position of the match *)
  brmr_ctor : EcSymbols.symbol;               (* constructor of the branch *)
}

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): resolve the position and the constructor
   (failing as before the migration), then apply the framed rule when the
   framing condition holds, the [rmatch] transformation through the
   bdhoare transformation rule otherwise. *)
let t_bdhoare_rmatch (r : bdhoare_rmatch_rule) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let at, j = EcPlRCond.resolve_rmatch !!tc env r.brmr_at r.brmr_ctor bhs.bhs_s in
  if EcPlRCond.rmatch_can_frame env ~can_frame:(can_frame bhs) at bhs.bhs_s then
    t_bdhoare_rmatch_framed { brmf_at = at; brmf_ctor = j } tc
  else
    let tr = EcTrRMatch.TrRMatch { trrm_at = at; trrm_ctor = j } in
    EcBdHoareTransform.t_bdhoare_transform { btr_tr = tr } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS]. Type the position in
   its memory, then apply the tactic. *)
let process_bdhoare_rmatch
    (c : EcSymbols.symbol) (at : EcParsetree.pcodepos1) (tc : tcenv1)
=
  let at = tc1_process_codepos1 tc (None, at) in
  t_bdhoare_rmatch { brmr_at = at; brmr_ctor = c } tc
