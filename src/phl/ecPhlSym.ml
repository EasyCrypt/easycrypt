(* -------------------------------------------------------------------- *)
(* Symmetry(commutativity) rule for equiv                               *)

(*  
 *  c2 ~ c1 : fun m2 m1 -> P m1 m2 ==> fun m2 m1 -> Q m1 m2
 *  --------------------------------------------------------
 *      c1 ~ c2 : P ==> Q
 *)

open EcFol
open EcBaseLogic
open EcLogic
open EcCorePhl

class rn_equiv_sym =
object
  inherit xrule "[hl] sym"
end

let rn_equiv_sym = RN_xtd (new rn_equiv_sym)

let build_sym ml mr pr po = 
  let s = Fsubst.f_bind_mem Fsubst.f_subst_id ml mr in
  let s = Fsubst.f_subst (Fsubst.f_bind_mem s mr ml) in
  s pr, s po

let t_equivF_sym g = 
  let concl = get_concl g in
  let ef    = t_as_equivF concl in
  let pr,po = build_sym mleft mright ef.ef_pr ef.ef_po in
  let cond = f_equivF pr ef.ef_fr ef.ef_fl po in
  prove_goal_by [cond] rn_equiv_sym g

let t_equivS_sym g = 
  let concl = get_concl g in
  let es    = t_as_equivS concl in
  let pr,po = build_sym (fst es.es_ml) (fst es.es_mr) es.es_pr es.es_po in
  let cond  = f_equivS_r {
    es_ml = fst es.es_ml, snd es.es_mr;
    es_mr = fst es.es_mr, snd es.es_ml;
    es_sl = es.es_sr; 
    es_sr = es.es_sl;
    es_pr = pr; 
    es_po = po } in
  prove_goal_by [cond] rn_equiv_sym g

let t_equiv_sym g = 
  match (get_concl g).f_node with
  | FequivF _ -> t_equivF_sym g
  | FequivS _ -> t_equivS_sym g
  | _ -> tacerror (NotPhl None)

let process_equiv_sym = t_equiv_sym

    

