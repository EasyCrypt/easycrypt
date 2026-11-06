(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare [wp] rule as supplied by the caller: high
   level, the split position is still a symbolic code gap (or absent: the
   longest wp-able suffix) that must be resolved. *)
type bdhoare_wp_rule = {
  bwr_at     : EcMatching.Position.codegap1 option;   (* split position *)
  bwr_uselet : bool;                                   (* let-bind the wp *)
}

(* Low-level parameters recorded in the proof-node: the split position is
   the RESOLVED integer index. *)
type bdhoare_wp_node = {
  bwn_at     : EcMatching.Position.nm_codegap1;   (* resolved split index *)
  bwn_uselet : bool;
}

type EcCoreGoal.rule += RBdHoareWp of bdhoare_wp_node

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: split the statement at the
   resolved index and replace the suffix by its wp. Its side condition (the
   suffix is entirely wp-able) is part of it, so the checker re-validates
   it. *)
let bdhoare_wp_subgoals (hyps : LDecl.hyps) (bhs : bdHoareS) (n : bdhoare_wp_node) =
  let s1, s2 = EcMatching.Position.split_at_nmcgap1 n.bwn_at bhs.bhs_s in
  let r, pre =
    EcPlWp.wp ~uselet:n.bwn_uselet
      hyps bhs.bhs_m (EcModules.stmt s2) (POE.empty (bhs_po bhs).inv) in
  if not (List.is_empty r) then
    failwith "bdhoare-wp: the suffix is not wp-able";
  let post = { m = fst bhs.bhs_m; inv = pre; } in
  [f_bdHoareS (snd bhs.bhs_m) (bhs_pr bhs) (EcModules.stmt s1)
     post bhs.bhs_cmp (bhs_bd bhs)]

(* -------------------------------------------------------------------- *)
(* Rule (TCB): resolve the split index (the env-dependent step: the code
   gap when given, the length of the prefix that wp cannot traverse
   otherwise), record the resolved node, and build its subgoal through the
   shared core. *)
let t_bdhoare_wp (r : bdhoare_wp_rule) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let bhs  = tc1_as_bdhoareS tc in
  let s_hd, s_wp = o_split (LDecl.toenv hyps) r.bwr_at bhs.bhs_s in
  let rm, _ =
    EcPlWp.wp ~uselet:r.bwr_uselet
      hyps bhs.bhs_m (EcModules.stmt s_wp) (POE.empty (bhs_po bhs).inv) in
  EcPlWp.check_wp_progress tc r.bwr_at rm;
  let n = { bwn_at     = List.length s_hd + List.length rm;
            bwn_uselet = r.bwr_uselet; } in
  FApi.xrule1 tc (RBdHoareWp n) (bdhoare_wp_subgoals hyps bhs n)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareWp n ->
         Some (EcPlRecheck.checker_of "bdhoare-wp" pf_as_bdhoareS
                 (fun hyps bhs -> bdhoare_wp_subgoals hyps bhs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS]. No position or a
   single one; positions are typed in the ambient environment. *)
let process_bdhoare_wp (cpos : EcParsetree.pdocodegap1) tc =
  let cpos = omap (EcTyping.trans_dcodegap1 (FApi.tc1_env tc)) cpos in
  match cpos with
  | None            -> t_bdhoare_wp { bwr_at = None  ; bwr_uselet = true } tc
  | Some (Single i) -> t_bdhoare_wp { bwr_at = Some i; bwr_uselet = true } tc
  | Some (Double _) -> tc_error_noXhl ~kinds:[`Equiv `Stmt] !!tc
