(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcParsetree
open EcTypes
open EcFol
open EcAst
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare [seq] rule as supplied by the caller: high level,
   the split position is still a symbolic code gap that must be resolved.

   The prefix [s1] is split on the event [r]: with probability bounded by
   [f1] (resp. [g1]) it ends in [r] (resp. [!r]), and from there the suffix
   [s2] reaches the post with probability bounded by [f2] (resp. [g2]);
   [phi] is an invariant established by [s1]. *)
type bdhoare_seq_rule = {
  bsr_at  : EcMatching.Position.codegap1;   (* split position *)
  bsr_phi : ss_inv;                          (* invariant after the prefix *)
  bsr_r   : ss_inv;                          (* event splitting the prefix *)
  bsr_f1  : ss_inv;                          (* bound for [r] after the prefix *)
  bsr_f2  : ss_inv;                          (* bound for the suffix from [r] *)
  bsr_g1  : ss_inv;                          (* bound for [!r] after the prefix *)
  bsr_g2  : ss_inv;                          (* bound for the suffix from [!r] *)
}

(* Low-level parameters recorded in the proof-node: as [bdhoare_seq_rule], but
   the split position is the RESOLVED integer index. *)
type bdhoare_seq_node = {
  bsn_at  : EcMatching.Position.nm_codegap1;   (* resolved split index *)
  bsn_phi : ss_inv;
  bsn_r   : ss_inv;
  bsn_f1  : ss_inv;
  bsn_f2  : ss_inv;
  bsn_g1  : ss_inv;
  bsn_g2  : ss_inv;
}

type EcCoreGoal.rule += RBdHoareSeq of bdhoare_seq_node

(* -------------------------------------------------------------------- *)
(* Pure low-level core shared by the rule and its checker. Needs no
   environment — code resolution happened upstream, in the rule. The
   subgoals for a branch whose prefix bound ([f1] / [g1]) or suffix bound
   ([f2] / [g2]) is syntactically [0%r] are omitted. The two reals bound in
   the non-modification subgoal are fresh at each call: the checker compares
   up to alpha-conversion. *)
let bdhoare_seq_subgoals (bhs : bdHoareS) (n : bdhoare_seq_node) : form list =
  let m   = fst bhs.bhs_m in
  let phi = ss_inv_rebind n.bsn_phi m in
  let pR  = ss_inv_rebind n.bsn_r   m in
  let f1  = ss_inv_rebind n.bsn_f1  m in
  let f2  = ss_inv_rebind n.bsn_f2  m in
  let g1  = ss_inv_rebind n.bsn_g1  m in
  let g2  = ss_inv_rebind n.bsn_g2  m in
  let s1, s2 = EcMatching.Position.split_at_nmcgap1 n.bsn_at bhs.bhs_s in
  let s1, s2 = stmt s1, stmt s2 in
  let nR = map_ss_inv1 f_not pR in
  let mt = snd bhs.bhs_m in
  let post = POE.lift phi in
  let cond_phi = f_hoareS mt (bhs_pr bhs) s1 post in
  let condf1 = f_bdHoareS mt (bhs_pr bhs) s1 pR bhs.bhs_cmp f1 in
  let condg1 = f_bdHoareS mt (bhs_pr bhs) s1 nR bhs.bhs_cmp g1 in
  let condf2 = f_bdHoareS mt (map_ss_inv2 f_and_simpl phi pR) s2 (bhs_po bhs) bhs.bhs_cmp f2 in
  let condg2 = f_bdHoareS mt (map_ss_inv2 f_and_simpl phi nR) s2 (bhs_po bhs) bhs.bhs_cmp g2 in
  let bd =
    (map_ss_inv2 f_real_add_simpl (map_ss_inv2 f_real_mul_simpl f1 f2) (map_ss_inv2 f_real_mul_simpl g1 g2)) in
  let condbd =
    match bhs.bhs_cmp with
    | FHle -> map_ss_inv2 f_real_le bd (bhs_bd bhs)
    | FHeq -> map_ss_inv2 f_eq bd (bhs_bd bhs)
    | FHge -> map_ss_inv2 f_real_le (bhs_bd bhs) bd in
  let condbd = map_ss_inv2 f_imp (bhs_pr bhs) condbd in
  let (ir1, ir2) = EcIdent.create "r", EcIdent.create "r" in
  let (r1 , r2 ) = f_local ir1 treal, f_local ir2 treal in
  let condnm =
    let eqs = map_ss_inv2 f_and (map_ss_inv1 ((EcUtils.flip f_eq) r1) f2)
                                (map_ss_inv1 ((EcUtils.flip f_eq) r2) g2) in
    let post = empty_hs eqs in
    f_forall
      [(ir1, GTty treal); (ir2, GTty treal)]
      (f_hoareS (snd bhs.bhs_m)
         (map_ss_inv2 f_and (bhs_pr bhs) eqs) s1 post)
  in
  let conds = [EcSubst.f_forall_mems_ss_inv bhs.bhs_m condbd; condnm] in
  let conds =
    if   f_equal g1.inv f_r0
    then condg1 :: conds
    else if   f_equal g2.inv f_r0
         then condg2 :: conds
         else condg1 :: condg2 :: conds in

  let conds =
    if   f_equal f1.inv f_r0
    then condf1 :: conds
    else if   f_equal f2.inv f_r0
         then condf2 :: conds
         else condf1 :: condf2 :: conds in

  cond_phi :: conds

(* -------------------------------------------------------------------- *)
(* Rule (TCB): resolve the code gap to an index (the env-dependent step),
   record the resolved node, and build its subgoals through the shared core.
   The non-modification subgoal (last) is left open; see [t_bdhoare_seq_full]. *)
let t_bdhoare_seq (r : bdhoare_seq_rule) tc =
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let n   = { bsn_at  = s_split_index env r.bsr_at bhs.bhs_s;
              bsn_phi = r.bsr_phi;
              bsn_r   = r.bsr_r;
              bsn_f1  = r.bsr_f1;
              bsn_f2  = r.bsr_f2;
              bsn_g1  = r.bsr_g1;
              bsn_g2  = r.bsr_g2; } in
  FApi.xrule1 tc (RBdHoareSeq n) (bdhoare_seq_subgoals bhs n)

(* -------------------------------------------------------------------- *)
(* Checker: rerun ONLY the low-level core on the recorded node (see
   [EcPhlRecheck]). *)
let () =
  register_rule_checker
    (function
     | RBdHoareSeq n ->
         Some (EcPhlRecheck.checker_of "bdhoare-seq" pf_as_bdhoareS
                 (fun _hyps bhs -> bdhoare_seq_subgoals bhs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): the rule, then a best-effort discharge of its last
   (non-modification) subgoal, which holds trivially when the prefix does not
   write the bounds [f2] / [g2]. This is what the surface [seq] tactic and the
   legacy positional entry (EcPhlSeq.t_bdhoare_seq) use.

   TEMPORARY: depends on the not-yet-migrated [EcPhlConseq]. *)
let t_bdhoare_seq_full (r : bdhoare_seq_rule) tc =
  let tactic tc =
    let hs  = tc1_as_hoareS tc in
    let tt1 =
      EcPhlConseq.t_hoareS_conseq_nm
        (hs_pr hs)
        { hsi_m = (fst hs.hs_m); hsi_inv = POE.empty f_true; }
    in
    let tt2 = EcPhlAuto.t_pl_trivial in
    FApi.t_seqs [tt1; tt2; t_fail] tc
  in

  FApi.t_last
    (FApi.t_try (t_intros_s_seq (`Symbol ["_"; "_"]) tactic))
    (t_bdhoare_seq r tc)

(* -------------------------------------------------------------------- *)
(* Elaboration of the optional bound information of a bdhoare [seq]. Returns
   the invariant [phi] and the bounds [f1], [f2], [g1], [g2]. *)
let process_bd_info (bd_info : p_seq_xt_info) tc =
  match bd_info with
  | PSeqNone ->
      let hs = tc1_as_bdhoareS tc in
      let m = fst hs.bhs_m in
      let f1, f2 = bhs_bd hs, {m;inv=f_r1} in
        (* The last argument will not be used *)
        ({m;inv=f_true}, f1, f2, {m;inv=f_r0}, {m;inv=f_r1})

  | PSeqSingle f ->
      let hs = tc1_as_bdhoareS tc in
      let m = fst hs.bhs_m in
      let f  = snd (TTC.tc1_process_Xhl_form tc treal f) in
      let f1, f2 = (map_ss_inv2 f_real_div (bhs_bd hs) f, f) in
        ({m;inv=f_true}, f1, f2, {m;inv=f_r0}, {m;inv=f_r1})

  | PSeqMult (phi, f1, f2, g1, g2) ->
    let hs = tc1_as_bdhoareS tc in
    let m = fst hs.bhs_m in
      let phi =
        phi |> omap (fun f -> snd (TTC.tc1_process_Xhl_formula tc f))
            |> odfl {m;inv=f_true} in

      let check_0 f =
        if not (f_equal f f_r0) then
          tc_error !!tc "the formula must be 0%%r" in

      let process_f (f1,f2) =
        match f1, f2 with
        | None, None -> assert false

        | Some fp, None ->
            let _, f = TTC.tc1_process_Xhl_form tc treal fp in
            reloc fp.pl_loc check_0 f.inv; (f, {m;inv=f_r1})

        | None, Some fp ->
            let _, f = TTC.tc1_process_Xhl_form tc treal fp in
            reloc fp.pl_loc check_0 f.inv; ({m;inv=f_r1}, f)

        | Some f1, Some f2 ->
            let _, f1 = TTC.tc1_process_Xhl_form tc treal f1 in
            let _, f2 = TTC.tc1_process_Xhl_form tc treal f2 in
            (f1, f2)
      in

      let f1, f2 = process_f (f1, f2) in
      let g1, g2 = process_f (g1, g2) in

      (phi, f1, f2, g1, g2)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS]. Validate the seq surface
   syntax for that logic (no side, single position and event), type the event,
   the bound information and the split position, then apply the rule. *)
let process_bdhoare_seq (info : seq_info) tc =
  let i =
    match info.seqi_at with
    | Single i -> i
    | Double _ -> tc_error !!tc "seq: a single position is expected" in
  if is_some info.seqi_side then
    tc_error !!tc "seq: no side information expected";
  let r =
    match info.seqi_mid with
    | Single r -> r
    | Double _ -> tc_error !!tc "seq: a single formula is expected" in
  let _, r = TTC.tc1_process_Xhl_formula tc r in
  let (phi, f1, f2, g1, g2) = process_bd_info info.seqi_bd tc in
  let i = EcLowPhlGoal.tc1_process_codegap1 tc (info.seqi_side, i) in
  t_bdhoare_seq_full
    { bsr_at = i; bsr_phi = phi; bsr_r = r;
      bsr_f1 = f1; bsr_f2 = f2; bsr_g1 = g1; bsr_g2 = g2; } tc
