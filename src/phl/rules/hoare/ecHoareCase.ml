(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the hoare [case] rule: the case formula, and whether it is
   conjoined to the precondition with the simplifying conjunction. Already
   typed, nothing to resolve: the same record is the rule argument and the
   node payload. *)
type hoare_case = {
  hca_cond     : ss_inv;
  hca_simplify : bool;
}

type EcCoreGoal.rule += RHoareCase of hoare_case

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. *)
let hoare_case_subgoals (hs : sHoareS) (n : hoare_case) : form list =
  let fand = if n.hca_simplify then f_and_simpl else f_and in
  let f    = ss_inv_rebind n.hca_cond (fst hs.hs_m) in
  let mt   = snd hs.hs_m in
  let a = f_hoareS mt (map_ss_inv2 fand (hs_pr hs) f) hs.hs_s (hs_po hs) in
  let b = f_hoareS mt
            (map_ss_inv2 fand (hs_pr hs) (map_ss_inv1 f_not f))
            hs.hs_s (hs_po hs) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoare_case (r : hoare_case) (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  FApi.xrule1 tc (RHoareCase r) (hoare_case_subgoals hs r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareCase n ->
         Some (EcPlRecheck.checker_of "hoare-case" pf_as_hoareS
                 (fun _hyps hs -> hoare_case_subgoals hs n))
     | _ -> None)
