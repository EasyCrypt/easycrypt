(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare [case] rule: the case formula, and whether it
   is conjoined to the precondition with the simplifying conjunction.
   Already typed, nothing to resolve: the same record is the rule argument
   and the node payload. *)
type bdhoare_case = {
  bca_cond     : ss_inv;
  bca_simplify : bool;
}

type EcCoreGoal.rule += RBdHoareCase of bdhoare_case

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. *)
let bdhoare_case_subgoals (bhs : bdHoareS) (n : bdhoare_case) : form list =
  let fand = if n.bca_simplify then f_and_simpl else f_and in
  let f    = ss_inv_rebind n.bca_cond (fst bhs.bhs_m) in
  let mt   = snd bhs.bhs_m in
  let concl pre =
    f_bdHoareS mt pre bhs.bhs_s (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in
  let a = concl (map_ss_inv2 fand (bhs_pr bhs) f) in
  let b = concl (map_ss_inv2 fand (bhs_pr bhs) (map_ss_inv1 f_not f)) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_bdhoare_case (r : bdhoare_case) (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  FApi.xrule1 tc (RBdHoareCase r) (bdhoare_case_subgoals bhs r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareCase n ->
         Some (EcPlRecheck.checker_of "bdhoare-case" pf_as_bdhoareS
                 (fun _hyps bhs -> bdhoare_case_subgoals bhs n))
     | _ -> None)
