(* -------------------------------------------------------------------- *)
open EcAst
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* The [circuit] rules live in [rules/<logic>/] ([EcHoareCircuit],
   [EcEquivCircuit], [EcHoareCircuitSimplify], [EcHoareExtens]) and, for
   the ones on formulas, in [rules/fol/] ([EcFolCircuit], [EcFolExtens]).
   This module only keeps the dispatchers and the derived [extens]. *)
let t_bdep_solve (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS _ -> EcHoareCircuit.t_hoare_circuit tc
  | FequivS _ -> EcEquivCircuit.t_equiv_circuit tc
  | _         -> EcFolCircuit.t_fol_circuit tc

(* -------------------------------------------------------------------- *)
let t_bdep_simplify (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS _ -> EcHoareCircuitSimplify.t_hoare_circuit_simplify tc
  | _ -> assert false

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): the [extens] rule of the goal (enumeration of
   the values of a program variable, or of an [all p (iota_ s n)]), then
   [tt] on each of its premises, in order, which must close it. *)
let t_extens (v : string option) (tt : FApi.backward) (tc : tcenv1) =
  let lap = EcCircuits.stopwatch (FApi.tc1_env tc) in

  let t_rule =
    match (FApi.tc1_goal tc).f_node, v with
    | FhoareS _, Some v -> EcHoareExtens.t_hoare_extens { her_var = v }
    | _, None -> EcFolExtens.t_fol_extens
    | _ -> tc_error !!tc "Wrong goal shape"
  in

  let t_close (g : tcenv1) =
    match FApi.t_try_base tt g with
    | `Failure e -> tc_error_exn !!tc e
    | `Success g -> begin
      match FApi.tc_opened g with
      | [] -> g
      | hd :: _ ->
        tc_error !!tc "Failed to close goal:@. %a"
          EcPrinting.(pp_form PPEnv.(ofenv (FApi.tc1_env tc)))
          (FApi.get_pregoal_by_id hd (FApi.tc_penv g)).g_concl
    end
  in

  let tc = FApi.t_onall t_close (t_rule tc) in
  lap "Extens"; tc
