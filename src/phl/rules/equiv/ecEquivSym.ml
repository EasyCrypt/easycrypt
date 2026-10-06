(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The equiv [sym] rules have no parameters. *)
type EcCoreGoal.rule +=
  | REquivSSym
  | REquivFSym

(* -------------------------------------------------------------------- *)
(* Pure cores shared by the rules and their checkers: exchange the two
   programs (and memory types), and swap the memories of the pre- and
   postcondition. They need no environment and have no side condition. *)
let equivS_sym_subgoals (es : equivS) : form list =
  let (ml, mtl), (mr, mtr) = es.es_ml, es.es_mr in
  let pr = { ml; mr; inv = (ts_inv_rebind (es_pr es) mr ml).inv } in
  let po = { ml; mr; inv = (ts_inv_rebind (es_po es) mr ml).inv } in
  [f_equivS mtr mtl pr es.es_sr es.es_sl po]

let equivF_sym_subgoals (ef : equivF) : form list =
  let ml, mr = ef.ef_ml, ef.ef_mr in
  let pr = { ml; mr; inv = (ts_inv_rebind (ef_pr ef) mr ml).inv } in
  let po = { ml; mr; inv = (ts_inv_rebind (ef_po ef) mr ml).inv } in
  [f_equivF pr ef.ef_fr ef.ef_fl po]

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_equivS_sym (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  FApi.xrule1 tc REquivSSym (equivS_sym_subgoals es)

let t_equivF_sym (tc : tcenv1) =
  let ef = tc1_as_equivF tc in
  FApi.xrule1 tc REquivFSym (equivF_sym_subgoals ef)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivSSym ->
         Some (EcPlRecheck.checker_of "equivS-sym" pf_as_equivS
                 (fun _hyps es -> equivS_sym_subgoals es))
     | REquivFSym ->
         Some (EcPlRecheck.checker_of "equivF-sym" pf_as_equivF
                 (fun _hyps ef -> equivF_sym_subgoals ef))
     | _ -> None)
