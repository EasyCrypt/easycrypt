(* -------------------------------------------------------------------- *)
open EcFol
open EcEnv

open EcCoreGoal
open EcLowCircuits
open EcCircuits
open EcPlCircuit

(* -------------------------------------------------------------------- *)
(* The [circuit] rule on formulas has no parameters: the decision is a
   function of the goal. *)
type EcCoreGoal.rule += RFolCircuit

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: it runs the circuit
   decision (no subgoal), raising [CircuitInvalid] (or [CircError]) when
   it does not establish the goal, so the checker re-runs the decision. *)
let fol_circuit_subgoals (hyps : LDecl.hyps) (f : form) : form list =
  let ctxt = LDecl.tohyps hyps in
  assert (ctxt.h_tvar = []);
  let st = circuit_state_of_hyps hyps in
  let cgoal = circuit_of_form st hyps f |> state_close_circuit st in
  if not (circ_valid cgoal) then raise CircuitInvalid;
  []

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_fol_circuit (tc : tcenv1) =
  let sg =
    try  fol_circuit_subgoals (FApi.tc1_hyps tc) (FApi.tc1_goal tc) with
    | CircuitInvalid ->
      tc_error !!tc "Failed to solve goal through circuit reasoning@\n"
    | CircError err ->
      tc_error !!tc "circuit solve failed with error: %a"
        (pp_circ_error EcPrinting.PPEnv.(ofenv (FApi.tc1_env tc)))
        err
  in FApi.xrule1 tc RFolCircuit sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RFolCircuit ->
         Some (EcPlRecheck.checker_of "fol-circuit" (fun _ f -> f)
                 fol_circuit_subgoals)
     | _ -> None)
