(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the equiv [rndsem] rule as supplied by the caller: high
   level, the position is still a symbolic code gap that must be resolved. *)
type equiv_rndsem_rule = {
  ersr_side   : side;                            (* rewritten side *)
  ersr_at     : EcMatching.Position.codegap1;   (* start of the suffix *)
  ersr_reduce : bool;                            (* sample only the variables of Q *)
}

(* Low-level parameters recorded in the proof-node: the position is the
   RESOLVED integer index. *)
type equiv_rndsem_node = {
  ersn_side   : side;
  ersn_at     : EcMatching.Position.nm_codegap1;   (* resolved index *)
  ersn_reduce : bool;
}

type EcCoreGoal.rule += REquivRndSem of equiv_rndsem_node

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: replace the suffix of the
   chosen side by its semantic sampling. Its side condition (a straight-line
   suffix writing no global) is part of it, so the checker re-validates it. *)
let equiv_rndsem_subgoals
    (hyps : LDecl.hyps) (es : equivS) (n : equiv_rndsem_node)
=
  let env = LDecl.toenv hyps in
  let s, m =
    match n.ersn_side with
    | `Left  -> es.es_sl, es.es_ml
    | `Right -> es.es_sr, es.es_mr in
  let s1, s2 = EcMatching.Position.split_at_nmcgap1 n.ersn_at s in
  let fv =
    if   n.ersn_reduce
    then Some (EcPV.PV.fv env (fst m) (es_po es).inv)
    else None in
  let (_, mt), s2 = EcPlRndSem.semrnd env m fv s2 in
  let s = stmt (s1 @ s2) in
  match n.ersn_side with
  | `Left  -> [f_equivS mt (snd es.es_mr) (es_pr es) s es.es_sr (es_po es)]
  | `Right -> [f_equivS (snd es.es_ml) mt (es_pr es) es.es_sl s (es_po es)]

(* -------------------------------------------------------------------- *)
(* Rule (TCB): resolve the code gap to an index, record the resolved node,
   and build its subgoal through the shared core. *)
let t_equiv_rndsem (r : equiv_rndsem_rule) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_equivS tc in
  let s   = sideif r.ersr_side es.es_sl es.es_sr in
  let n   = { ersn_side   = r.ersr_side;
              ersn_at     = s_split_index env r.ersr_at s;
              ersn_reduce = r.ersr_reduce; } in
  let sg =
    try  equiv_rndsem_subgoals (FApi.tc1_hyps tc) es n
    with EcPlRndSem.InvalidSemRnd -> tc_error !!tc "semrnd" in
  FApi.xrule1 tc (REquivRndSem n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivRndSem n ->
         Some (EcPlRecheck.checker_of "equiv-rndsem" pf_as_equivS
                 (fun hyps es -> equiv_rndsem_subgoals hyps es n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS]. The position is typed
   first, in the memory of the side (which then makes an unsided call fail
   there), then the rule is applied. *)
let process_equiv_rndsem ~reduce (side : oside) pos (tc : tcenv1) =
  let pos = tc1_process_codegap1 tc (side, pos) in
  match side with
  | None -> tc_error !!tc "invalid arguments"
  | Some side ->
      t_equiv_rndsem { ersr_side = side; ersr_at = pos; ersr_reduce = reduce } tc
