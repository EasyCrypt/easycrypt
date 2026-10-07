(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The hoare [match] rule has no parameters: the statement is the
   [match]. *)
type EcCoreGoal.rule += RHoareMatch

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (the
   statement is a single [match]) is part of it, so the checker
   re-validates it. The constructors are read from the environment. *)
let hoare_match_subgoals (hyps : LDecl.hyps) (hs : sHoareS) : form list =
  let e, bs =
    match hs.hs_s.s_node with
    | [{ i_node = Smatch (e, bs) }] -> (e, bs)
    | _ -> failwith "hoare-match: the statement is not a single match" in
  let concl (mb : EcPlMatch.match_branch) =
    f_hoareS (snd mb.mb_mem)
      (map_ss_inv2 f_and mb.mb_cond (hs_pr hs)) mb.mb_body (hs_po hs) in
  List.map concl
    (EcPlMatch.match_branches (LDecl.toenv hyps) hs.hs_m e bs)

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoare_match (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let sg =
    try  hoare_match_subgoals (FApi.tc1_hyps tc) hs
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc RHoareMatch sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareMatch ->
         Some (EcPlRecheck.checker_of "hoare-match" pf_as_hoareS
                 hoare_match_subgoals)
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): on [match e with ... end; c], push [c] into the
   branches (when not empty), then apply the rule. *)
let t_hoare_match_head (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let _, c = tc1_first_match tc hs.hs_s in
  if List.is_empty c.s_node then t_hoare_match tc else
    FApi.t_seq
      (EcHoareTransform.t_hoare_transform
         { htr_tr = EcTrMatchPush.TrMatchPush })
      t_hoare_match tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS]. *)
let process_hoare_match (_ : matchmode) (tc : tcenv1) =
  t_hoare_match_head tc
