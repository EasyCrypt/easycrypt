(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the ehoare [case] rule: the case formula. Already typed,
   nothing to resolve: the same record is the rule argument and the node
   payload. *)
type ehoare_case = {
  ehca_cond : ss_inv;
}

type EcCoreGoal.rule += REHoareCase of ehoare_case

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. *)
let ehoare_case_subgoals (hs : eHoareS) (n : ehoare_case) : form list =
  let f  = ss_inv_rebind n.ehca_cond (fst hs.ehs_m) in
  let mt = snd hs.ehs_m in
  let pre f = map_ss_inv2 f_interp_ehoare_form f (ehs_pr hs) in
  let a = f_eHoareS mt (pre f) hs.ehs_s (ehs_po hs) in
  let b = f_eHoareS mt (pre (map_ss_inv1 f_not f)) hs.ehs_s (ehs_po hs) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_ehoare_case (r : ehoare_case) (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  FApi.xrule1 tc (REHoareCase r) (ehoare_case_subgoals hs r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareCase n ->
         Some (EcPlRecheck.checker_of "ehoare-case" pf_as_ehoareS
                 (fun _hyps hs -> ehoare_case_subgoals hs n))
     | _ -> None)
