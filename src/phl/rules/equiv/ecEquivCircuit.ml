(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal
open EcLowCircuits
open EcCircuits
open EcPlCircuit

(* -------------------------------------------------------------------- *)
(* The equiv [circuit] rule has no parameters: the decision is a function
   of the goal. *)
type EcCoreGoal.rule += REquivCircuit

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: it runs the circuit
   decision (no subgoal), raising [CircuitInvalid] (or [CircError]) when
   it does not establish the judgement, so the checker re-runs the
   decision. *)
let equiv_circuit_subgoals (hyps : LDecl.hyps) (es : equivS) : form list =
  let env = LDecl.toenv hyps in
  let lap = stopwatch env in

  let st = create_state (EcEnv.gstate env) in

  let st = circuit_state_of_hyps ~st hyps in
  let st = circuit_state_of_memenv ~st env es.es_ml in
  let st = circuit_state_of_memenv ~st env es.es_mr in

  let st, cpres = process_pre hyps ~st (es_pr es).inv in
  lap "Done with precondition processing";

  (* Circuits from pvars are tagged by memory so we can just put
     everything in one state *)
  let st = state_of_prog hyps (fst es.es_ml) ~st es.es_sl.s_node in
  lap "Done with left program circuit gen";

  let st = state_of_prog hyps (fst es.es_mr) ~st es.es_sr.s_node in
  lap "Done with right program circuit gen";

  if not (solve_post ~st ~pres:cpres hyps (es_po es).inv) then
    raise CircuitInvalid;
  []

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_equiv_circuit (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_circuit_subgoals (FApi.tc1_hyps tc) es with
    | CircuitInvalid ->
      tc_error !!tc "failed to verify postcondition"
    | CircError err ->
      tc_error !!tc "circuit solve failed with error: %a"
        (pp_circ_error EcPrinting.PPEnv.(ofenv (FApi.tc1_env tc)))
        err
  in FApi.xrule1 tc REquivCircuit sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivCircuit ->
         Some (EcPlRecheck.checker_of "equiv-circuit" pf_as_equivS
                 equiv_circuit_subgoals)
     | _ -> None)
