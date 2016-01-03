(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcEnv

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module Sid = EcIdent.Sid

(* -------------------------------------------------------------------- *)
module LowInternal = struct
 let t_gen_cond side e tc =
   let hyps  = FApi.tc1_hyps tc in
   let fresh = ["&m"; "&m"; "_"; "_"; "_"] in
   let fresh = LDecl.fresh_ids hyps fresh in

   let m1,m2,h,h1,h2 = as_seq5 fresh in
   let t_introm = if is_none side then t_id else t_intros_i [m1] in

   let t_sub b tc =
     FApi.t_on1seq 0
       (EcPhlRCond.t_rcond side b 1)
       (FApi.t_seqs
           [t_introm; EcPhlSkip.t_skip; t_intros_i [m2;h];
            FApi.t_or
              (FApi.t_seqs [t_elim_hyp h;
                            t_intros_i [h1;h2];
                            t_apply_hyp h2])
              (t_apply_hyp h)])
       tc
   in

   FApi.t_seqsub (EcPhlCase.t_hl_case e) [t_sub true; t_sub false] tc
end

(* -------------------------------------------------------------------- *)
let t_hoare_cond tc =
  let hs = tc1_as_hoareS tc in
  let (e,_,_) = fst (tc1_first_if tc hs.hs_s) in
  LowInternal.t_gen_cond None (form_of_expr (EcMemory.memory hs.hs_m) e) tc

(* -------------------------------------------------------------------- *)
let t_bdhoare_cond tc =
  let bhs = tc1_as_bdhoareS tc in
  let (e,_,_) = fst (tc1_first_if tc bhs.bhs_s) in
  LowInternal.t_gen_cond None (form_of_expr (EcMemory.memory bhs.bhs_m) e) tc

(* -------------------------------------------------------------------- *)
let rec t_equiv_cond side tc =
  let hyps = FApi.tc1_hyps tc in
  let es   = tc1_as_equivS tc in

  match side with
  | Some s ->
      let e =
        match s with
        | `Left ->
          let (e,_,_) = fst (tc1_first_if tc es.es_sl) in
          form_of_expr (EcMemory.memory es.es_ml) e
        | `Right ->
          let (e,_,_) = fst (tc1_first_if tc es.es_sr) in
          form_of_expr (EcMemory.memory es.es_mr) e
      in LowInternal.t_gen_cond side e tc

  | None ->
      let el,_,_ = fst (tc1_first_if tc es.es_sl) in
      let er,_,_ = fst (tc1_first_if tc es.es_sr) in
      let el     = form_of_expr (EcMemory.memory es.es_ml) el in
      let er     = form_of_expr (EcMemory.memory es.es_mr) er in
      let fiff   =
        f_forall_mems
          [es.es_ml;es.es_mr]
          (f_imp es.es_pr (f_iff el er)) in

      let fresh = ["hiff";"&m1";"&m2";"h";"h";"h"] in
      let fresh = LDecl.fresh_ids hyps fresh in

      let hiff,m1,m2,h,h1,h2 = as_seq6 fresh in

      let t_aux =
        let rwpt = { pt_head = PTLocal hiff;
                     pt_args = [PAMemory m1; PAMemory m2; PASub None]; } in


        FApi.t_seqs [t_intros_i [m1]    ; EcPhlSkip.t_skip;
                     t_intros_i [m2; h] ; t_elim_hyp h;
                     t_intros_i [h1; h2];
                     FApi.t_seqsub
                       (t_rewrite rwpt (`RtoL, None))
                       [t_apply_hyp h1; t_apply_hyp h2]]
      in
        FApi.t_on1seq 1 (t_cut fiff)
          (t_intros_i_seq [hiff]
             (FApi.t_seqsub
                (t_equiv_cond (Some `Left))
                [FApi.t_seqsub
                   (EcPhlRCond.Low.t_equiv_rcond `Right true  1)
                   [t_aux; t_clear hiff];
                 FApi.t_seqsub
                   (EcPhlRCond.Low.t_equiv_rcond `Right false 1)
                   [t_aux; t_clear hiff]]))
          tc

(* -------------------------------------------------------------------- *)
let process_cond info tc =
  let default_if i s = ofdfl (fun _ -> tc1_pos_last_if tc s) i in
  
  match info with
  | `Head side ->
    t_hS_or_bhS_or_eS ~th:t_hoare_cond ~tbh:t_bdhoare_cond ~te:(t_equiv_cond side) tc

  | `Seq (side, i1, i2, f) -> 
    let es = tc1_as_equivS tc in
    let f  = EcProofTyping.tc1_process_prhl_formula tc f in
    let n1 = default_if i1 es.es_sl in
    let n2 = default_if i2 es.es_sr in
    FApi.t_seqsub (EcPhlApp.t_equiv_app (n1,n2) f)
      [ t_id; t_equiv_cond side ] tc

  | `SeqOne (s, i, f1, f2) -> 
    let es = tc1_as_equivS tc in
    let n = default_if i (match s with `Left -> es.es_sl | `Right -> es.es_sr) in
    let f1 = EcProofTyping.tc1_process_phl_formula ~side:s tc f1 in
    let f2 = EcProofTyping.tc1_process_phl_formula ~side:s tc f2 in
    FApi.t_seqsub
      (EcPhlApp.t_equiv_app_onesided s n f1 f2)
      [ t_id; t_bdhoare_cond] tc
