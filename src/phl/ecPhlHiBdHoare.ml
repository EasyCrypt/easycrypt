(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcEnv

open EcCoreGoal
open EcLowGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let process_bdhoare_split info tc =
  let hyps, concl = FApi.tc1_flat tc in

  let (penv, qenv), pr, po =
    match concl.f_node with
    | FbdHoareS bhs ->
        let hyps = LDecl.push_active bhs.bhs_m hyps in
          ((hyps, hyps), bhs.bhs_pr, bhs.bhs_po)

    | FbdHoareF bhf ->
        (LDecl.hoareF bhf.bhf_f hyps, bhf.bhf_pr, bhf.bhf_po)

    | _ ->
        tc_error !!tc "the conclusion must be a bdhoare judgment" in

  match info with
  | EcParsetree.BDH_split_bop (b1, b2, b3) ->
      let t =
             if is_and po then EcPhlBdHoare.t_bdhoare_and
        else if is_or  po then EcPhlBdHoare.t_bdhoare_or
        else
          tc_error !!tc
            "the postcondition must be a conjunction or a disjunction"
      in

      let b1 = TTC.pf_process_form !!tc penv treal b1 in
      let b2 = TTC.pf_process_form !!tc penv treal b2 in
      let b3 = b3 |> omap (TTC.pf_process_form !!tc penv treal) |> odfl f_r0 in

      t b1 b2 b3 tc

  | EcParsetree.BDH_split_or_case (b1, b2, f) ->
      let b1 = TTC.pf_process_form !!tc penv treal b1 in
      let b2 = TTC.pf_process_form !!tc penv treal b2 in
      let f  = TTC.pf_process_form !!tc qenv tbool f  in

      let t_conseq po lemma tactic =
        let rwtt tc =
          let pt = ptglobal ~tys:[] lemma in

          let rwtt = [
            EcLowGoal.t_intros_i [EcIdent.create "_"];
            EcHiGoal.LowRewrite.t_rewrite (`LtoR, None, None) pt;
            t_true;
          ] in FApi.t_seqs rwtt tc
        in

        FApi.t_seqsub
          (EcPhlConseq.t_conseq pr po)
          [t_true; rwtt; tactic]
      in

      t_conseq
        (f_or (f_and f po) (f_and (f_not f) po))
        (EcCoreLib.CI_Logic.mk_logic "orDandN")
        (FApi.t_on1seq 3
           (EcPhlBdHoare.t_bdhoare_or b1 b2 f_r0)
           (t_conseq
              f_false
              (EcCoreLib.CI_Logic.mk_logic "andDorN")
              EcHiGoal.process_trivial))
        tc

  | EcParsetree.BDH_split_not (b1, b2) ->
      let b1 = b1 |> omap (TTC.pf_process_form !!tc penv treal) |> odfl f_r1 in
      let b2 = TTC.pf_process_form !!tc penv treal b2 in
      EcPhlBdHoare.t_bdhoare_not b1 b2 tc
