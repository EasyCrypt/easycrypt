(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcPV
open EcCorePhl
open EcCoreHiLogic

(* -------------------------------------------------------------------- *)
(* Transitivity rule for equiv                                          *)

(*  forall m1 m3, P m1 m3 => exists m2, P1 m1 m2 /\ P2 m2 m3
 *  forall m1 m2 m3, Q1 m1 m2 => Q2 m2 m3 => Q m1 m3
 *  c1 ~ c2 : P1 ==> Q1
 *  c2 ~ c3 : P2 ==> Q2
 *  --------------------------------------------------------
 *      c1 ~ c3 : P ==> Q
 * Remark: the most basic rule is normally 
 *   Q = exists m2, Q1 m1 m2 /\ Q2 m2 m3
 * => the actual rule is in fact this basic rule + conseq
 * I prefer this more convenient one
 *)

(* -------------------------------------------------------------------- *)
class rn_equiv_trans =
object
  inherit xrule "[hl] trans"
end

let rn_equiv_trans = RN_xtd (new rn_equiv_trans)

(* -------------------------------------------------------------------- *)
module Low = struct
  let transitivity_side_cond hyps prml prmr poml pomr 
      p q p1 q1 pomt p2 q2 = 
    let env = LDecl.toenv hyps in
    let cond1 = 
      let fv1 = PV.fv env mright p1 in
      let fv2 = PV.fv env mleft  p2 in
      let fv  = PV.union fv1 fv2 in
      let elts,glob = PV.elements fv in
      let bd, s = generalize_subst env mhr elts glob in
      let s1 = PVM.of_mpv s mright in 
      let s2 = PVM.of_mpv s mleft in 
      let concl = f_and (PVM.subst env s1 p1) (PVM.subst env s2 p2) in
      f_forall_mems [prml;prmr] (f_imp p (f_exists bd concl)) in
    let cond2 = 
      let m2 = LDecl.fresh_id hyps "&m" in
      let q1 = Fsubst.f_subst_mem mright m2 q1 in
      let q2 = Fsubst.f_subst_mem mleft  m2 q2 in
      f_forall_mems [poml;(m2,pomt);pomr] (f_imps [q1;q2] q) in
    cond1, cond2 
  
  let t_equivS_trans (mt,c2) p1 q1 p2 q2 g =
    let hyps,concl = get_goal g in
    let es     = t_as_equivS concl in
    let m1, m3 = es.es_ml, es.es_mr in
    let cond1, cond2 = 
      transitivity_side_cond hyps m1 m3 m1 m3
        es.es_pr es.es_po p1 q1 mt p2 q2 in
    let cond3 = 
      f_equivS_r { es with
        es_mr = (mright,mt); es_sr = c2;
        es_pr = p1; es_po = q1 } in
    let cond4 = 
      f_equivS_r { es with
        es_ml = (mleft,mt); es_sl = c2;
        es_pr = p2; es_po = q2 } in
    prove_goal_by [cond1;cond2;cond3;cond4] rn_equiv_trans g
  
  let t_equivF_trans f p1 q1 p2 q2 g =
    let env,hyps,concl = get_goal_e g in
    let ef     = t_as_equivF concl in
    let (prml,prmr), (poml,pomr) = Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
    let _,(_,pomt) = Fun.hoareF_memenv f env in
    let cond1, cond2 = 
      transitivity_side_cond hyps prml prmr poml pomr
        ef.ef_pr ef.ef_po p1 q1 pomt p2 q2 in
    let cond3 = f_equivF p1 ef.ef_fl f q1 in
    let cond4 = f_equivF p2 f ef.ef_fr q2 in
    prove_goal_by [cond1;cond2;cond3;cond4] rn_equiv_trans g
end

(* -------------------------------------------------------------------- *)
let process_trans_stmt s c p1 q1 p2 q2 g = 
  let hyps,concl = get_goal g in
  let es = t_as_equivS concl in
  let mt = snd (if oget s then es.es_ml else es.es_mr) in
  let p1,q1 = 
    let hyps = LDecl.push_all [es.es_ml; (mright, mt)] hyps in
    process_form hyps p1 tbool, process_form hyps q1 tbool in
  let p2,q2 = 
    let hyps = LDecl.push_all [(mleft, mt); es.es_mr] hyps in
    process_form hyps p2 tbool, process_form hyps q2 tbool in
  (* Translation of the stmt *)
  let c = EcCoreHiPhl.process_prhl_stmt (oget s) g c in
  Low.t_equivS_trans (mt,c) p1 q1 p2 q2 g 

let process_trans_fun f p1 q1 p2 q2 g = 
  let env,hyps,concl = get_goal_e g in
  let ef = t_as_equivF concl in
  let f = EcTyping.trans_gamepath env f in
  let (_,prmt),(_,pomt) = Fun.hoareF_memenv f env in
  let (prml,prmr), (poml,pomr) = Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
  let process ml mr fo = 
    process_form (LDecl.push_all [ml; mr] hyps) fo tbool in
  let p1 = process prml (mright, prmt) p1 in
  let q1 = process poml (mright, pomt) q1 in
  let p2 = process (mleft,prmt) prmr p2 in
  let q2 = process (mleft,pomt) pomr q2 in
    Low.t_equivF_trans f p1 q1 p2 q2 g 
      
let process_equiv_trans (tk, p1, q1, p2, q2) g =
  match tk with
  | TKfun f -> process_trans_fun f p1 q1 p2 q2 g
  | TKstmt (s, c) -> process_trans_stmt s c p1 q1 p2 q2 g
