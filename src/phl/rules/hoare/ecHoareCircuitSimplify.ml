(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal
open EcCircuits
open EcPlCircuit

(* -------------------------------------------------------------------- *)
(* The hoare [circuit simplify] rule has no parameters: the simplified
   postcondition is a function of the goal. *)
type EcCoreGoal.rule += RHoareCircuitSimplify

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: it re-runs the circuit
   simplification of the postcondition, so the checker compares the
   recorded premise with its result. Raises [CircuitExceptions] when the
   exceptional postconditions are not empty. *)
let hoare_circuit_simplify_subgoals (hyps : LDecl.hyps) (hs : sHoareS) :
    form list =
  if not (POE.is_empty (hs_po hs).hsi_inv) then
    raise CircuitExceptions;

  let env = LDecl.toenv hyps in
  let m = fst hs.hs_m in
  let lap = stopwatch env in
  let st = circuit_state_of_hyps hyps in
  let st = circuit_state_of_memenv ~st env hs.hs_m in
  let st, pres = process_pre hyps ~st (hs_pr hs).inv in
  lap "Done with precondition processing";

  let st = state_of_prog ~st hyps m hs.hs_s.s_node in
  let post =
    EcCallbyValue.norm_cbv (circ_red hyps) hyps (POE.lower (hs_po hs)).inv
  in

  lap "Done with first simplify";
  let f = circ_simplify_form_bitstring_equality ~st ~pres hyps post in
  lap "Done with circuit simplify";
  let f = EcCallbyValue.norm_cbv EcReduction.full_red hyps f in
  lap "Done with second simplify";
  [f_hoareS (snd hs.hs_m) {inv = (hs_pr hs).inv; m} hs.hs_s
     (POE.lift {inv = f; m})]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoare_circuit_simplify (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  if not (POE.is_empty (hs_po hs).hsi_inv) then
    tc_error !!tc "exceptions not supported";
  let sg =
    try  hoare_circuit_simplify_subgoals (FApi.tc1_hyps tc) hs with
    | CircError err ->
      tc_error !!tc "Circuit simplify failed with error: %a"
        (pp_circ_error EcPrinting.PPEnv.(ofenv (FApi.tc1_env tc)))
        err
  in FApi.xrule1 tc RHoareCircuitSimplify sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareCircuitSimplify ->
         Some (EcPlRecheck.checker_of "hoare-circuit-simplify" pf_as_hoareS
                 hoare_circuit_simplify_subgoals)
     | _ -> None)
