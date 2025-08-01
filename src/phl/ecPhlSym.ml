(*-------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal
open EcLowPhlGoal
open EcAst

(*-------------------------------------------------------------------- *)
let t_equivF_sym tc =
  let ef    = tc1_as_equivF tc in
  let mr, ml = ef.ef_ml, ef.ef_mr in
  let pr    = {ml;mr;inv=(ef_pr ef).inv} in
  let po    = {ml;mr;inv=(ef_po ef).inv} in
  let cond  = f_equivF pr ef.ef_fr ef.ef_fl po in
  FApi.xmutate1 tc `EquivSym [cond]

(*-------------------------------------------------------------------- *)
let t_equivS_sym tc =
  let es    = tc1_as_equivS tc in
  let (mr, mtr), (ml, mtl) = es.es_ml, es.es_mr in
  let pr    = {ml;mr;inv=(es_pr es).inv} in
  let po    = {ml;mr;inv=(es_po es).inv} in
  let cond  = f_equivS mtl mtr pr es.es_sr es.es_sl po in

  FApi.xmutate1 tc `EquivSym [cond]

(*-------------------------------------------------------------------- *)
let t_equiv_sym tc =
  match (FApi.tc1_goal tc).f_node with
  | FequivF _ -> t_equivF_sym tc
  | FequivS _ -> t_equivS_sym tc
  | _ -> tc_error_noXhl ~kinds:[`Equiv `Any] !!tc
