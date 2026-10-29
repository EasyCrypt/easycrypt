(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal
open EcPlWeakMem

(* -------------------------------------------------------------------- *)
(* Parameters of the equiv [weakmem] rule: the side whose memory is
   weakened and the variables declared in it, typed. Nothing to resolve:
   the same record is the rule argument and the node payload. *)
type equiv_weakmem = {
  ewm_side : side;
  ewm_vars : ovariable list;
}

type EcCoreGoal.rule += REquivWeakMem of equiv_weakmem

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   variables are the last ones declared in the memory of the side, fresh
   in the rest of it, and not used by the judgement on that side) are
   re-checked by [EcPlWeakMem.restrict], so the checker re-validates
   them. *)
let equiv_weakmem_subgoals
    (hyps : LDecl.hyps) (es : equivS) (n : equiv_weakmem)
=
  let env = LDecl.toenv hyps in
  let me, s = sideif n.ewm_side (es.es_ml, es.es_sl) (es.es_mr, es.es_sr) in
  let me = restrict env n.ewm_vars me
             (used env (fst me) s [es.es_pr; es.es_po]) in
  let es =
    match n.ewm_side with
    | `Left  -> { es with es_ml = me }
    | `Right -> { es with es_mr = me } in
  [f_equivS_r es]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_equiv_weakmem (r : equiv_weakmem) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_weakmem_subgoals (FApi.tc1_hyps tc) es r
    with InvalidWeakening msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REquivWeakMem r) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivWeakMem n ->
         Some (EcPlRecheck.checker_of "equiv-weakmem" pf_as_equivS
                 (fun hyps es -> equiv_weakmem_subgoals hyps es n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): cut the hypothesis [h] weakened by the
   variables on the given side(s) (both when [side] is [None]: the right
   memory first, then the left one), reduce the cut judgement to [h] by
   the rule on each weakened side and close it by [h]. Raises
   [EcMemory.DuplicatedMemoryBinding] (before acting) when a variable is
   already declared. *)
let t_equiv_weakmem_hyp
    (h : EcIdent.t) (side : oside) (xs : ovariable list) (tc : tcenv1)
=
  let es = destr_equivS (LDecl.hyp_by_id h (FApi.tc1_hyps tc)) in
  let sides = match side with None -> [`Right; `Left] | Some s -> [s] in
  let weaken es = function
    | `Left  -> { es with es_ml = EcMemory.bindall xs es.es_ml }
    | `Right -> { es with es_mr = EcMemory.bindall xs es.es_mr } in
  let es = List.fold_left weaken es sides in
  let t_rule s = t_equiv_weakmem { ewm_side = s; ewm_vars = xs } in
  FApi.t_first
    (FApi.t_seqs
       (List.map t_rule sides @ [EcLowGoal.t_apply_hyp h ~args:[] ~sk:0]))
    (EcLowGoal.t_cut (f_equivS_r es) tc)
