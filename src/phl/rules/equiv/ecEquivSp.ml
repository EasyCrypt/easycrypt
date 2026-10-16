(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The equiv [sp] rule has no parameters: it is stated on the whole
   statements, which must be sp-able. *)
type EcCoreGoal.rule += REquivSp

(* -------------------------------------------------------------------- *)
(* Two-sided strongest postcondition: the left statement first, then the
   right one. Returns the parts of the statements that are not sp-able. *)
let equiv_sp env (es : equivS) (sl : instr list) (sr : instr list) =
  let mc = (fst es.es_ml, fst es.es_mr) in
  let restl, sp = EcPlSp.sp_stmt ~mc es.es_ml env sl (es_pr es).inv in
  let restr, sp = EcPlSp.sp_stmt ~mc es.es_mr env sr sp in
  (restl, restr), sp

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (both
   statements are sp-able, the postcondition is their strongest
   postcondition) are part of it, so the checker re-validates them. *)
let equiv_sp_subgoals (hyps : LDecl.hyps) (es : equivS) : form list =
  let env = LDecl.toenv hyps in
  let (restl, restr), sp = equiv_sp env es es.es_sl.s_node es.es_sr.s_node in
  if not (List.is_empty restl && List.is_empty restr) then
    failwith "equiv-sp: the statements are not sp-able";
  if not (EcReduction.is_conv hyps sp (es_po es).inv) then
    failwith "equiv-sp: the postcondition is not the strongest postcondition";
  []

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_equiv_sp (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let subgoals =
    try  equiv_sp_subgoals (FApi.tc1_hyps tc) es
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc REquivSp subgoals

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivSp ->
         Some (EcPlRecheck.checker_of "equiv-sp" pf_as_equivS
                 equiv_sp_subgoals)
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): compute the longest sp-able prefixes [c1] /
   [c1'] of the statements up to [at], split there with the [seq] rule
   using [sp(c1, c1', P)] as intermediate relation, and close the first
   premise with the rule. *)
let t_equiv_sp_prefix (at : EcMatching.Position.codegap1 pair option) tc =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_equivS tc in
  let sl1, _ = o_split ~rev:true env (omap fst at) es.es_sl in
  let sr1, _ = o_split ~rev:true env (omap snd at) es.es_sr in
  let (restl, restr), sp = equiv_sp env es sl1 sr1 in
  EcPlSp.check_sp_progress ~side:`Left  tc (is_some at) restl;
  EcPlSp.check_sp_progress ~side:`Right tc (is_some at) restr;
  let kl = List.length sl1 - List.length restl in
  let kr = List.length sr1 - List.length restr in
  let r  = EcEquivSeq.{
    esr_at  = (EcPlSp.gap_at kl, EcPlSp.gap_at kr);
    esr_mid = { ml = fst es.es_ml; mr = fst es.es_mr; inv = sp }; } in
  FApi.t_seqsub (EcEquivSeq.t_equiv_seq r) [t_equiv_sp; EcLowGoal.t_id] tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS], the positions (if
   any) are a pair. *)
let process_equiv_sp (at : EcParsetree.pcodegap1 pair option) tc =
  let env = FApi.tc1_env tc in
  let at  = Option.map (pair_map (EcTyping.trans_codegap1 env)) at in
  t_equiv_sp_prefix at tc
