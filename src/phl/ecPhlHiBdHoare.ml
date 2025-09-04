(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcAst

open EcCoreGoal
open EcLowGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let process_bdhoare_split info tc =
  let _, concl = FApi.tc1_flat tc in

  let pr, po =
    match concl.f_node with
    | FbdHoareS bhs ->
        (bhs_pr bhs, bhs_po bhs)

    | FbdHoareF bhf ->
        (bhf_pr bhf, bhf_po bhf)

    | _ ->
        tc_error !!tc "the conclusion must be a bdhoare judgment" in

  match info with
  | EcParsetree.BDH_split_bop (b1, b2, b3) ->
      let t =
             if is_and po.inv then EcPhlBdHoare.t_bdhoare_and
        else if is_or  po.inv then EcPhlBdHoare.t_bdhoare_or
        else
          tc_error !!tc
            "the postcondition must be a conjunction or a disjunction"
      in
      let _,b1 = TTC.tc1_process_Xhl_form tc treal b1 in
      let _,b2 = TTC.tc1_process_Xhl_form tc treal b2 in
      let b3 = b3 |> omap (fun f -> snd ( TTC.tc1_process_Xhl_form tc treal f)) |> odfl {m=b1.m;inv=f_r0} in

      t b1 b2 b3 tc

  | EcParsetree.BDH_split_or_case (b1, b2, f) ->
      let _, b1 = TTC.tc1_process_Xhl_form tc treal b1 in
      let _, b2 = TTC.tc1_process_Xhl_form tc treal b2 in
      let _, f  = TTC.tc1_process_Xhl_formula tc f in

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
          (EcPhlConseq.t_conseq (Inv_ss pr) (Inv_ss po))
          [t_true; rwtt; tactic]
      in

      t_conseq
        (map_ss_inv2 f_or (map_ss_inv2 f_and f po) (map_ss_inv2 f_and (map_ss_inv1 f_not f) po))
        (EcCoreLib.CI_Logic.mk_logic "orDandN")
        (FApi.t_on1seq 3
           (EcPhlBdHoare.t_bdhoare_or b1 b2 {m=b1.m;inv=f_r0})
           (t_conseq
              {inv=f_false;m=b1.m}
              (EcCoreLib.CI_Logic.mk_logic "andDorN")
              EcHiGoal.process_trivial))
        tc

  | EcParsetree.BDH_split_not (b1, b2) ->
    let _,b2 = TTC.tc1_process_Xhl_form tc treal b2 in
    let b1 = b1 |> omap (fun f -> snd (TTC.tc1_process_Xhl_form tc treal f)) |> odfl {m=b2.m;inv=f_r1} in
    EcPhlBdHoare.t_bdhoare_not b1 b2 tc
