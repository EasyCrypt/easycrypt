(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The bdhoare [match] rule has no parameters: the statement is the
   [match]. *)
type EcCoreGoal.rule += RBdHoareMatch

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (the
   statement is a single [match]) is part of it, so the checker
   re-validates it. The constructors are read from the environment. *)
let bdhoare_match_subgoals (hyps : LDecl.hyps) (bhs : bdHoareS) : form list =
  let e, bs =
    match bhs.bhs_s.s_node with
    | [{ i_node = Smatch (e, bs) }] -> (e, bs)
    | _ -> failwith "bdhoare-match: the statement is not a single match" in
  let concl (mb : EcPlMatch.match_branch) =
    f_bdHoareS (snd mb.mb_mem)
      (map_ss_inv2 f_and mb.mb_cond (bhs_pr bhs)) mb.mb_body
      (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in
  List.map concl
    (EcPlMatch.match_branches (LDecl.toenv hyps) bhs.bhs_m e bs)

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_bdhoare_match (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  let sg =
    try  bdhoare_match_subgoals (FApi.tc1_hyps tc) bhs
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc RBdHoareMatch sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareMatch ->
         Some (EcPlRecheck.checker_of "bdhoare-match" pf_as_bdhoareS
                 bdhoare_match_subgoals)
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): on [match e with ... end; c], push [c] into the
   branches (when not empty), then apply the rule. *)
let t_bdhoare_match_head (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  let _, c = tc1_first_match tc bhs.bhs_s in
  if List.is_empty c.s_node then t_bdhoare_match tc else
    FApi.t_seq
      (EcBdHoareTransform.t_bdhoare_transform
         { btr_tr = EcTrMatchPush.TrMatchPush })
      t_bdhoare_match tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS]. *)
let process_bdhoare_match (_ : matchmode) (tc : tcenv1) =
  t_bdhoare_match_head tc
