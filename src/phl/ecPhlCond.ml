(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcEnv
open EcLogic
open EcCorePhl

module Sid = EcIdent.Sid

(* -------------------------------------------------------------------- *)
module LowInternal = struct
 let t_gen_cond side e g =
   let hyps = get_hyps g in
   let m1,m2,h,h1,h2 = as_seq5 (LDecl.fresh_ids hyps ["&m";"&m";"_";"_";"_"]) in
   let t_introm = if side <> None then t_intros_i [m1] else t_id None in
   let t_sub b g = 
     t_seq_subgoal (EcPhlRCond.t_rcond side b 1)
       [t_lseq
           [t_introm; EcPhlSkip.t_skip; t_intros_i [m2;h];
            t_or  
              (t_lseq [t_elim_hyp h; t_intros_i [h1;h2]; t_hyp h2])
              (t_hyp h)
           ];
        t_id None] g
   in
     t_seq_subgoal (EcPhlCase.t_hl_case e) [t_sub true; t_sub false] g
end

(* -------------------------------------------------------------------- *)
let t_hoare_cond g = 
  let concl = get_concl g in
  let hs = t_as_hoareS concl in 
  let (e,_,_) = fst (s_first_if "if" hs.hs_s) in
    LowInternal.t_gen_cond None (form_of_expr (EcMemory.memory hs.hs_m) e) g

let t_bdHoare_cond g = 
  let concl = get_concl g in
  let bhs = t_as_bdHoareS concl in 
  let (e,_,_) = fst (s_first_if "if" bhs.bhs_s) in
    LowInternal.t_gen_cond None (form_of_expr (EcMemory.memory bhs.bhs_m) e) g

let rec t_equiv_cond side g =
  let hyps,concl = get_goal g in
  let es = t_as_equivS concl in
  match side with
  | Some s ->
      let e = 
        if s then 
          let (e,_,_) = fst (s_first_if "if" es.es_sl) in
          form_of_expr (EcMemory.memory es.es_ml) e
        else
          let (e,_,_) = fst (s_first_if "if" es.es_sr) in
          form_of_expr (EcMemory.memory es.es_mr) e in
      LowInternal.t_gen_cond side e g

  | None -> 
      let el,_,_ = fst (s_first_if "if" es.es_sl) in
      let er,_,_ = fst (s_first_if "if" es.es_sr) in
      let el = form_of_expr (EcMemory.memory es.es_ml) el in
      let er = form_of_expr (EcMemory.memory es.es_mr) er in
      let fiff = f_forall_mems [es.es_ml;es.es_mr] (f_imp es.es_pr (f_iff el er)) in
      let hiff,m1,m2,h,h1,h2 = 
        match LDecl.fresh_ids hyps ["hiff";"&m1";"&m2";"h";"h";"h"] with 
        | [hiff;m1;m2;h;h1;h2] -> hiff,m1,m2,h,h1,h2 
        | _ -> assert false in
      let t_aux = 
        t_lseq [t_intros_i [m1];
                EcPhlSkip.t_skip;
                t_intros_i [m2;h];
                t_elim_hyp h;
                t_intros_i [h1;h2];
                t_seq_subgoal (t_rewrite_hyp `RtoL hiff 
                                 [AAmem m1;AAmem m2;AAnode])
                  [t_hyp h1; t_hyp h2]] in
      t_seq_subgoal (t_cut fiff)
        [ t_id None;
          t_seq (t_intros_i [hiff])
            (t_seq_subgoal (t_equiv_cond (Some true))
               [t_seq_subgoal (EcPhlRCond.Low.t_equiv_rcond false true  1) 
                   [t_aux; t_clear hiff];
                t_seq_subgoal (EcPhlRCond.Low.t_equiv_rcond false false 1) 
                  [t_aux; t_clear hiff]
               ])
        ] g

(* -------------------------------------------------------------------- *)
let process_cond side g =
  let concl = get_concl g in
  let check_N () = 
    if side <> None then
      cannot_apply "cond" "Unexpected side in non relational goal" in
  if is_equivS concl then t_equiv_cond side g
  else begin 
    check_N ();
    if is_hoareS concl then t_hoare_cond g
    else if is_bdHoareS concl then t_bdHoare_cond g
    else cannot_apply "cond" "the conclusion is not a hoare or a equiv goal"
  end
