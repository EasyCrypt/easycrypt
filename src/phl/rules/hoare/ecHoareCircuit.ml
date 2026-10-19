(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal
open EcLowCircuits
open EcCircuits
open EcPlCircuit

(* -------------------------------------------------------------------- *)
(* The hoare [circuit] rule has no parameters: the decision is a function
   of the goal. *)
type EcCoreGoal.rule += RHoareCircuit

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: it runs the circuit
   decision (no subgoal), raising [CircuitExceptions] / [CircuitInvalid]
   (or [CircError]) when it does not establish the judgement, so the
   checker re-runs the decision. *)
let hoare_circuit_subgoals (hyps : LDecl.hyps) (hs : sHoareS) : form list =
  let env = LDecl.toenv hyps in
  let lap = stopwatch env in
  let st = create_state (EcEnv.gstate env) in
  let st = circuit_state_of_hyps ~st hyps in
  let st = circuit_state_of_memenv ~st env hs.hs_m in
  let st, cpres = process_pre hyps ~st (hs_pr hs).inv in
  lap "Done with precondition processing";

  (* Get open state *)
  let st = state_of_prog hyps (fst hs.hs_m) ~st hs.hs_s.s_node in
  lap "Done with program circuit gen";

  if not (POE.is_empty (hs_po hs).hsi_inv) then
    raise CircuitExceptions;

  let res = solve_post ~st ~pres:cpres hyps (POE.lower (hs_po hs)).inv in
  clear_translation_caches ();
  if not res then raise CircuitInvalid;
  []

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoare_circuit (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let sg =
    try  hoare_circuit_subgoals (FApi.tc1_hyps tc) hs with
    | CircuitExceptions ->
      tc_error !!tc "exception not supported"
    | CircuitInvalid ->
      tc_error !!tc "failed to verify postcondition"
    | CircError err ->
      tc_error !!tc "circuit solve failed with error: %a"
        (pp_circ_error EcPrinting.PPEnv.(ofenv (FApi.tc1_env tc)))
        err
  in FApi.xrule1 tc RHoareCircuit sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareCircuit ->
         Some (EcPlRecheck.checker_of "hoare-circuit" pf_as_hoareS
                 hoare_circuit_subgoals)
     | _ -> None)
