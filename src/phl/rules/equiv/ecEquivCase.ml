(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the equiv [case] rule: the case relation, and whether it is
   conjoined to the precondition with the simplifying conjunction. Already
   typed, nothing to resolve: the same record is the rule argument and the
   node payload. *)
type equiv_case = {
  eca_cond     : ts_inv;
  eca_simplify : bool;
}

type EcCoreGoal.rule += REquivCase of equiv_case

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. *)
let equiv_case_subgoals (es : equivS) (n : equiv_case) : form list =
  let fand = if n.eca_simplify then f_and_simpl else f_and in
  let f    = ts_inv_rebind n.eca_cond (fst es.es_ml) (fst es.es_mr) in
  let mtl, mtr = snd es.es_ml, snd es.es_mr in
  let concl pre = f_equivS mtl mtr pre es.es_sl es.es_sr (es_po es) in
  let a = concl (map_ts_inv2 fand (es_pr es) f) in
  let b = concl (map_ts_inv2 fand (es_pr es) (map_ts_inv1 f_not f)) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_equiv_case (r : equiv_case) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  FApi.xrule1 tc (REquivCase r) (equiv_case_subgoals es r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivCase n ->
         Some (EcPlRecheck.checker_of "equiv-case" pf_as_equivS
                 (fun _hyps es -> equiv_case_subgoals es n))
     | _ -> None)
