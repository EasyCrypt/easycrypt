(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameter of the bdhoare [exists] elimination rules: the maximal
   number of binders to eliminate ([None]: all of them, see
   [EcPlExists.prenex_exists]). Nothing to resolve: the same record is the
   rule argument and the node payload. *)
type bdhoare_exists_elim = {
  bxe_bound : int option;
}

type EcCoreGoal.rule +=
  | RBdHoareSExistsElim of bdhoare_exists_elim
  | RBdHoareFExistsElim of bdhoare_exists_elim

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rules and their checkers. *)
let bdhoareS_exists_elim_subgoals (bhs : bdHoareS) (n : bdhoare_exists_elim) =
  let pre = bhs_pr bhs in
  let bd, inv = EcPlExists.prenex_exists ?bound:n.bxe_bound pre.inv in
  [f_forall bd
     (f_bdHoareS (snd bhs.bhs_m) { pre with inv } bhs.bhs_s
        (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs))]

let bdhoareF_exists_elim_subgoals (bhf : bdHoareF) (n : bdhoare_exists_elim) =
  let pre = bhf_pr bhf in
  let bd, inv = EcPlExists.prenex_exists ?bound:n.bxe_bound pre.inv in
  [f_forall bd
     (f_bdHoareF { pre with inv } bhf.bhf_f
        (bhf_po bhf) bhf.bhf_cmp (bhf_bd bhf))]

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_bdhoareS_exists_elim (r : bdhoare_exists_elim) (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  FApi.xrule1 tc (RBdHoareSExistsElim r) (bdhoareS_exists_elim_subgoals bhs r)

let t_bdhoareF_exists_elim (r : bdhoare_exists_elim) (tc : tcenv1) =
  let bhf = tc1_as_bdhoareF tc in
  FApi.xrule1 tc (RBdHoareFExistsElim r) (bdhoareF_exists_elim_subgoals bhf r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareSExistsElim n ->
         Some (EcPlRecheck.checker_of "bdhoareS-exists-elim" pf_as_bdhoareS
                 (fun _hyps bhs -> bdhoareS_exists_elim_subgoals bhs n))
     | RBdHoareFExistsElim n ->
         Some (EcPlRecheck.checker_of "bdhoareF-exists-elim" pf_as_bdhoareF
                 (fun _hyps bhf -> bdhoareF_exists_elim_subgoals bhf n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node). *)
let t_bdhoare_exists_elim (r : bdhoare_exists_elim) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FbdHoareS _ -> t_bdhoareS_exists_elim r tc
  | FbdHoareF _ -> t_bdhoareF_exists_elim r tc
  | _           -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc

(* The consequence rule, whose premise on the precondition is closed by
   giving the values of [fs] as witnesses.

   TEMPORARY: the consequence rule still comes from the not-yet-migrated
   [EcPhlConseq]. *)
let t_bdhoare_exists_intro (fs : ss_inv list) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let xs   = EcPlExists.intro_binders (List.map (fun f -> Inv_ss f) fs) in
  let pre  = EcPlExists.intro_pre ~ehoare:false xs (tc1_get_pre tc) in
  let h    = LDecl.fresh_id hyps "h" in
  let m    = LDecl.fresh_id hyps "&m" in
  let args = List.map (fun f -> PAFormula (ss_inv_rebind f m).inv) fs in
  let t_pre =
    FApi.t_seqs [t_intros_i [m; h]; t_exists_intro_s args; t_apply_hyp h] in
  FApi.t_seqsub
    (EcPhlConseq.t_conseq pre (tc1_get_post tc))
    [t_pre; t_trivial; t_id]
    tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS] or a [bdHoareF]. *)
let process_bdhoare_exists_intro
    ~(elim : bool) (fs : EcParsetree.pformula list) (tc : tcenv1)
=
  let hyps, concl = FApi.tc1_flat tc in
  let penv, m =
    match concl.f_node with
    | FbdHoareF bhf -> fst (LDecl.hoareF bhf.bhf_m bhf.bhf_f hyps), bhf.bhf_m
    | FbdHoareS bhs -> LDecl.push_active_ss bhs.bhs_m hyps, fst bhs.bhs_m
    | _ -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc in
  let fs =
    List.map
      (fun f -> { m; inv = TTC.pf_process_form_opt !!tc penv None f })
      fs in
  if elim then
    FApi.t_seq
      (t_bdhoare_exists_intro fs)
      (t_bdhoare_exists_elim { bxe_bound = Some (List.length fs) })
      tc
  else t_bdhoare_exists_intro fs tc
