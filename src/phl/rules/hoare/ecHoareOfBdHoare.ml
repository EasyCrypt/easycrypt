(* -------------------------------------------------------------------- *)
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The rules deriving a hoare judgement from a probabilistic one have no
   parameters. *)
type EcCoreGoal.rule +=
  | RHoareSOfBdHoare
  | RHoareFOfBdHoare

(* -------------------------------------------------------------------- *)
(* Pure cores shared by the rules and their checkers. The side condition
   (no exceptional postcondition) is part of them, so the checker
   re-validates it. *)
let hoareS_of_bdhoare_subgoals (hs : sHoareS) : form list =
  let { main = inv } as post = (hs_po hs).hsi_inv in
  if not (POE.is_empty post) then
    failwith "hoareS-of-bdhoare: exceptional postconditions";
  let m = (hs_po hs).hsi_m in
  [f_bdHoareS (snd hs.hs_m) (hs_pr hs) hs.hs_s
     (map_ss_inv1 f_not { m; inv }) FHeq { m = fst hs.hs_m; inv = f_r0; }]

let hoareF_of_bdhoare_subgoals (hf : sHoareF) : form list =
  let { main = inv } as post = (hf_po hf).hsi_inv in
  if not (POE.is_empty post) then
    failwith "hoareF-of-bdhoare: exceptional postconditions";
  let m = (hf_po hf).hsi_m in
  [f_bdHoareF (hf_pr hf) hf.hf_f
     (map_ss_inv1 f_not { m; inv }) FHeq { m = hf.hf_m; inv = f_r0; }]

(* -------------------------------------------------------------------- *)
let no_exceptions tc = tc_error !!tc "Exceptions are not permitted"

(* Rules (TCB). *)
let t_hoareS_of_bdhoare (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  if not (POE.is_empty (hs_po hs).hsi_inv) then no_exceptions tc;
  FApi.xrule1 tc RHoareSOfBdHoare (hoareS_of_bdhoare_subgoals hs)

let t_hoareF_of_bdhoare (tc : tcenv1) =
  let hf = tc1_as_hoareF tc in
  if not (POE.is_empty (hf_po hf).hsi_inv) then no_exceptions tc;
  FApi.xrule1 tc RHoareFOfBdHoare (hoareF_of_bdhoare_subgoals hf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareSOfBdHoare ->
         Some (EcPlRecheck.checker_of "hoareS-of-bdhoare" pf_as_hoareS
                 (fun _hyps hs -> hoareS_of_bdhoare_subgoals hs))
     | RHoareFOfBdHoare ->
         Some (EcPlRecheck.checker_of "hoareF-of-bdhoare" pf_as_hoareF
                 (fun _hyps hf -> hoareF_of_bdhoare_subgoals hf))
     | _ -> None)
