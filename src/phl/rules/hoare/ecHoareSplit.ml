(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcFol
open EcLowPhlGoal
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): duplicate the precondition with the
   consequence rule, then split the postcondition with the conjunctive
   consequence rule.

   TEMPORARY: both consequence rules still come from the not-yet-migrated
   [EcPhlConseq]. *)
let t_hoare_split (tc : tcenv1) =
  let hoare = tc1_as_hoareS tc in
  let pre   = hs_pr hoare in
  let post  = POE.lower (hs_po hoare) in

  match sform_of_form post.inv with
  | SFand (`Sym, (f1, f2)) ->
    let dp = map_ss_inv2 f_and pre pre in
    let cl = update_hs_ss { post with inv = f1 } (hs_po hoare) in
    let cr = update_hs_ss { post with inv = f2 } (hs_po hoare) in

    EcPhlConseq.t_hoareS_conseq dp (hs_po hoare) tc
      |> FApi.t_firsts EcHiGoal.process_done 2
      |> FApi.as_tcenv1
      |> EcPhlConseq.t_hoareS_conseq_conj (hs_pr hoare) cr (hs_pr hoare) cl

  | _ ->
    tc_error !!tc "post-condition should be a conjunction"
