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
        if s then
          let (e,_,_) = fst (tc1_first_if tc es.es_sl) in
          form_of_expr (EcMemory.memory es.es_ml) e
        else
          let (e,_,_) = fst (tc1_first_if tc es.es_sr) in
          form_of_expr (EcMemory.memory es.es_mr) e in
      LowInternal.t_gen_cond side e tc

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
                (t_equiv_cond (Some true))
                [FApi.t_seqsub
                   (EcPhlRCond.Low.t_equiv_rcond false true  1)
                   [t_aux; t_clear hiff];
                 FApi.t_seqsub
                   (EcPhlRCond.Low.t_equiv_rcond false false 1)
                   [t_aux; t_clear hiff]]))
          tc

(* -------------------------------------------------------------------- *)
let process_cond side tc =
  let concl = FApi.tc1_goal tc in

  if   is_equivS concl
  then t_equiv_cond side tc
  else begin
    if not (is_none side) then
      tc_error !!tc "unexpected side in non relational goal";

         if is_hoareS   concl then t_hoare_cond   tc
    else if is_bdHoareS concl then t_bdhoare_cond tc
    else tc_error !!tc "the conclusion is not a hoare or a equiv goal"
  end
