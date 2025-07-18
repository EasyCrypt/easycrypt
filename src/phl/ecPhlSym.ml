(*-------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal
open EcLowPhlGoal
open EcSubst
open EcAst

(*-------------------------------------------------------------------- *)
let build_sym ml mr pr po =
  let s = Fsubst.f_subst_id in
  let s = Fsubst.f_bind_mem s ml mr in
  let s = Fsubst.f_bind_mem s mr ml in
  let s = Fsubst.f_subst s in
  (s pr, s po)

(*-------------------------------------------------------------------- *)
let t_equivF_sym tc =
  let ef    = tc1_as_equivF tc in
  let ml, mr = ef.ef_ml, ef.ef_mr in
  let pr    = ts_inv_rebind (ef_pr ef) mr ml in
  let po    = ts_inv_rebind (ef_po ef) mr ml in
  let cond  = f_equivF pr ef.ef_fr ef.ef_fl po in
  FApi.xmutate1 tc `EquivSym [cond]

(*-------------------------------------------------------------------- *)
let t_equivS_sym tc =
  let es    = tc1_as_equivS tc in
  let (ml, mtl), (mr, mtr) = es.es_ml, es.es_mr in
  let pr    = ts_inv_rebind (es_pr es) mr ml in
  let po    = ts_inv_rebind (es_po es) mr ml in
  let cond  = f_equivS mtr mtl pr es.es_sr es.es_sl po in

  FApi.xmutate1 tc `EquivSym [cond]

(*-------------------------------------------------------------------- *)
let t_equiv_sym tc =
  match (FApi.tc1_goal tc).f_node with
  | FequivF _ -> t_equivF_sym tc
  | FequivS _ -> t_equivS_sym tc
  | _ -> tc_error_noXhl ~kinds:[`Equiv `Any] !!tc
