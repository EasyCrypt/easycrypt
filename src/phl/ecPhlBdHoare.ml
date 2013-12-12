(* -------------------------------------------------------------------- *)
open EcTypes
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcCorePhl
open EcPhlConseq

(* -------------------------------------------------------------------- *)
class rn_hl_hoare_bd_hoare =
object
  inherit xrule "[hl] hoare-bd-hoare"
end

let rn_hl_hoare_bd_hoare =
  RN_xtd (new rn_hl_hoare_bd_hoare)

(* -------------------------------------------------------------------- *)
(* This are the 4 basic rules                                           *)
let errormsg = "bound is not = 0%r"

let hoare_of_bdhoareS g =
  let concl = get_concl g in
  let bhs = t_as_bdHoareS concl in
  if not (bhs.bhs_cmp = FHeq && f_equal bhs.bhs_bd f_r0) then 
    tacuerror "%s" errormsg;
  let concl = 
    f_hoareS bhs.bhs_m bhs.bhs_pr bhs.bhs_s (f_not bhs.bhs_po) in
  prove_goal_by [concl] rn_hl_hoare_bd_hoare g

let hoare_of_bdhoareF g =
  let concl = get_concl g in
  let bhf = t_as_bdHoareF concl in
  if not (bhf.bhf_cmp = FHeq && f_equal bhf.bhf_bd f_r0) then 
    tacuerror "%s" errormsg;
  let concl = 
    f_hoareF bhf.bhf_pr bhf.bhf_f (f_not bhf.bhf_po) in
  prove_goal_by [concl] rn_hl_hoare_bd_hoare g

let bdhoare_of_hoareS g =
  let concl = get_concl g in
  let hs = t_as_hoareS concl in
  let concl1 = f_bdHoareS hs.hs_m hs.hs_pr hs.hs_s (f_not hs.hs_po) FHeq f_r0 in
  prove_goal_by [concl1] rn_hl_hoare_bd_hoare g

let bdhoare_of_hoareF g =
  let concl = get_concl g in
  let hf = t_as_hoareF concl in
  let concl1 = f_bdHoareF hf.hf_pr hf.hf_f (f_not hf.hf_po) FHeq f_r0 in
  prove_goal_by [concl1] rn_hl_hoare_bd_hoare g

(* -------------------------------------------------------------------- *)
(* The top-level tactic                                                 *)
let t_hoare_bd_hoare g = 
  let concl = get_concl g in
  match concl.f_node with
  | FbdHoareF bhf ->
    if bhf.bhf_cmp = FHeq && f_equal bhf.bhf_bd f_r0 then 
      hoare_of_bdhoareF g
    else 
      t_seq_subgoal (t_bdHoareF_conseq_bd FHeq f_r0)
        [t_try EcPhlTrivial.t_trivial;
         hoare_of_bdhoareF] g

  | FbdHoareS bhs -> 
    if bhs.bhs_cmp = FHeq && f_equal bhs.bhs_bd f_r0 then 
       hoare_of_bdhoareS g
    else 
      t_seq_subgoal (t_bdHoareS_conseq_bd FHeq f_r0)
        [t_try EcPhlTrivial.t_trivial;
         hoare_of_bdhoareS] g
  | FhoareF _ -> bdhoare_of_hoareF g
  | FhoareS _ -> bdhoare_of_hoareS g
  | _ -> tacuerror "a hoare or phoare judgment was expected"
    
(* -------------------------------------------------------------------- *)
class rn_bdhoare_split =
object
  inherit xrule "[hl] bdhoare_split"
end

let rn_bdhoare_split =
  RN_xtd (new rn_bdhoare_split)

let t_bdhoare_split_bop 
    get_bdh mk_bdh destr_bop mk_bop
    b1 b2 b3 g =
  let concl = get_concl g in
  let bh,po,cmp,bd = get_bdh concl in
  let a,b = destr_bop po in
  let g1 = mk_bdh bh a cmp b1 in
  let g2 = mk_bdh bh b cmp b2 in
  let g3 = mk_bdh bh (mk_bop a b) (hoarecmp_opp cmp) b3 in
  let nb = f_real_sub (f_real_add b1 b2) b3 in
  assert (f_equal nb bd);
  prove_goal_by [g1;g2;g3] rn_bdhoare_split g

let t_bdhoare_split_bop_conseq 
    t_conseq_bd
    get_bdh mk_bdh destr_bop mk_bop
    b1 b2 b3 g =
  let _,_,cmp,b = get_bdh (get_concl g) in
  let nb = f_real_sub (f_real_add b1 b2) b3 in
  let t_main = 
    t_bdhoare_split_bop get_bdh mk_bdh destr_bop mk_bop
      b1 b2 b3 in
  if f_equal nb b then t_main g
  else t_seq_subgoal (t_conseq_bd cmp nb) [t_id None; t_main] g

let bdhoare_kind g = 
  match (get_concl g).f_node with
  | FbdHoareS _ -> true
  | FbdHoareF _ -> false
  | _           -> tacuerror "The conclusion should be a bdhoare judgment"

let gen_S = 
  let get_bdh g = 
    let bh = EcCorePhl.t_as_bdHoareS g in
    bh,bh.bhs_po, bh.bhs_cmp, bh.bhs_bd in
  let mk_bdh bh po cmp b = 
    f_bdHoareS_r { bh with bhs_po = po; bhs_cmp = cmp; bhs_bd = b } in
  fun tac -> tac EcPhlConseq.t_bdHoareS_conseq_bd get_bdh mk_bdh 

let gen_F = 
  let get_bdh g = 
    let bh = EcCorePhl.t_as_bdHoareF g in
    bh,bh.bhf_po, bh.bhf_cmp, bh.bhf_bd in   
  let mk_bdh bh po cmp b = 
    f_bdHoareF bh.bhf_pr bh.bhf_f po cmp b in
  fun tac -> tac EcPhlConseq.t_bdHoareF_conseq_bd get_bdh mk_bdh

let destr_and f = 
  try destr_and f 
  with DestrError _ -> tacuerror "The postcondition should be a conjunction"

let t_bdhoareS_and = gen_S t_bdhoare_split_bop_conseq destr_and f_or 
let t_bdhoareF_and = gen_F t_bdhoare_split_bop_conseq destr_and f_or 
let t_bdhoare_and b1 b2 b3 g =
  if bdhoare_kind g then t_bdhoareS_and b1 b2 b3 g
  else t_bdhoareF_and b1 b2 b3 g

let destr_or f = 
  try destr_or f 
  with DestrError _ -> tacuerror "The postcondition should be a disjunction"

let t_bdhoareS_or = gen_S t_bdhoare_split_bop_conseq destr_or f_and 
let t_bdhoareF_or = gen_F t_bdhoare_split_bop_conseq destr_or f_and 
let t_bdhoare_or b1 b2 b3 g = 
  if bdhoare_kind g then t_bdhoareS_or b1 b2 b3 g
  else t_bdhoareF_or b1 b2 b3 g

let t_bdhoare_split_not 
    get_bdh mk_bdh 
    b1 b2 g =
  let concl = get_concl g in
  let bh,po,cmp,bd = get_bdh concl in
  let g1 = mk_bdh bh f_true cmp b1 in
  let g2 = mk_bdh bh (f_not_simpl po) (hoarecmp_opp cmp) b2 in
  let nb = f_real_sub b1 b2 in
  assert (f_equal nb bd);
  prove_goal_by [g1;g2] rn_bdhoare_split g

let t_bdhoare_split_not_conseq 
    t_conseq_bd get_bdh mk_bdh 
    b1 b2 g =
  let _,_,cmp,b = get_bdh (get_concl g) in
  let nb = f_real_sub b1 b2 in
  let t_main = t_bdhoare_split_not get_bdh mk_bdh b1 b2  in
  if f_equal nb b then t_main g
  else t_seq_subgoal (t_conseq_bd cmp nb) [t_id None; t_main] g

let t_bdhoareS_not = gen_S t_bdhoare_split_not_conseq 
let t_bdhoareF_not = gen_F t_bdhoare_split_not_conseq 
let t_bdhoare_not b1 b2 g =
   if bdhoare_kind g then t_bdhoareS_not b1 b2 g 
   else t_bdhoareF_not b1 b2 g

open EcParsetree

let t_rewrite_glob s pqs = 
  let rwarg = (RWRw (s, None, None, [{ fp_kind = FPNamed(pqs,None); fp_args = []; }])) in
    EcHiLogic.process_rewrite pqs.EcLocation.pl_loc [(None, rwarg)]

let t_rewrite_logic s x = 
  let loc = EcLocation._dummy in
  let p   = EcLocation.mk_loc loc ([EcCoreLib.id_top; "Logic"], x) in
    t_rewrite_glob s p 
  
let process_bdhoare_split info g =
  let hyps, concl = get_goal g in
  let (penv, qenv), pr, po = 
    match concl.f_node with
    | FbdHoareS bhs -> 
      let hyps = LDecl.push_active bhs.bhs_m hyps in
      (hyps, hyps), bhs.bhs_pr, bhs.bhs_po
    | FbdHoareF bhf -> (LDecl.hoareF bhf.bhf_f hyps), bhf.bhf_pr, bhf.bhf_po
    | _ -> tacuerror "The conclusion should be a bdhoare judgment" in
  match info with
  | EcParsetree.BDH_split_bop(b1,b2,b3) ->
    let t =
      if is_and po then t_bdhoare_and
      else if is_or po then t_bdhoare_or
      else tacuerror 
        "The postcondition should be a conjunction or a disjunction" in
    let b1 = EcCoreHiLogic.process_form penv b1 treal in
    let b2 = EcCoreHiLogic.process_form penv b2 treal in
    let b3 = match b3 with
      | None -> f_r0
      | Some b3 -> EcCoreHiLogic.process_form penv b3 treal in
    t b1 b2 b3 g
  | EcParsetree.BDH_split_or_case(b1,b2,f) -> 
    let b1 = EcCoreHiLogic.process_form penv b1 treal in
    let b2 = EcCoreHiLogic.process_form penv b2 treal in
    let f  = EcCoreHiLogic.process_form qenv f tbool in
    let t_conseq po lemma tac =
      t_seq_subgoal (EcPhlConseq.t_conseq pr po)
        [EcLogic.t_true;
         EcLogic.t_lseq [
           EcLogic.t_intros_i [EcIdent.create "_"];
           t_rewrite_logic `LtoR lemma;
           t_true ];
         tac] in
    t_conseq (f_or (f_and f po) (f_and (f_not f) po)) "orDandN"
      (EcLogic.t_seq_subgoal (t_bdhoare_or b1 b2 f_r0)
         [t_id None;
          t_id None;
          t_id None;
          t_conseq f_false "andDorN" EcPhlTrivial.t_trivial]) g
    
  | EcParsetree.BDH_split_not (b1, b2) ->
    let b1 = match b1 with
      | None -> f_r1
      | Some b1 -> EcCoreHiLogic.process_form penv b1 treal in
    let b2 = EcCoreHiLogic.process_form penv b2 treal in
    t_bdhoare_not b1 b2 g
