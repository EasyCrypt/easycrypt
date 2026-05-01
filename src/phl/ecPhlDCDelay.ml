(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcCoreFol
open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Bridge between pRHL and delayed-coupling judgments.

   Semantically, with R1 = R2 = S1 = S2 = empty, the dcoupl definition
     exists mu, bind pi_i(mu) [[S_i]] = [[R_i; C_i]] m_i /\ Supp(mu) <= psi
   collapses to
     exists mu, pi_i(mu) = [[C_i]] m_i /\ Supp(mu) <= psi
   which is exactly the pRHL judgment.                                 *)

(* -------------------------------------------------------------------- *)

let s_cat a b = EcAst.stmt (a.EcAst.s_node @ b.EcAst.s_node)

module LowInternal = struct
  let s_empty = EcAst.stmt []

  (* equivS -> dcEquivS with R_i = S_i = eps *)
  let t_equivS_delay_r tc =
    let es = tc1_as_equivS tc in
    let pr = es_pr es in
    let po = es_po es in
    let concl =
      f_dcEquivS
        (snd es.es_ml) (snd es.es_mr) pr
        s_empty s_empty es.es_sl es.es_sr
        po s_empty s_empty
    in
    FApi.xmutate1 tc `Delay [concl]

  let t_equivS_delay = FApi.t_low0 "equivS-delay" t_equivS_delay_r

  (* equivF -> dcEquivF with R_i = S_i = eps *)
  let t_equivF_delay_r tc =
    let ef = tc1_as_equivF tc in
    let pr = ef_pr ef in
    let po = ef_po ef in
    let concl =
      f_dcEquivF pr
        s_empty ef.ef_fl s_empty
        s_empty ef.ef_fr s_empty
        po
    in
    FApi.xmutate1 tc `Delay [concl]

  let t_equivF_delay = FApi.t_low0 "equivF-delay" t_equivF_delay_r

  (* dcEquivS with empty S -> equivS *)
  let t_dcEquivS_undelay_r tc =
    let es = tc1_as_dcEquivS tc in
    let empty s = List.is_empty s.EcAst.s_node in
    if not (empty es.dces_sl) then
      tc_error !!tc ~who:"undelay" "left continuation S1 is not empty";
    if not (empty es.dces_sr) then
      tc_error !!tc ~who:"undelay" "right continuation S2 is not empty";
    let pr = dces_pr es in
    let po = dces_po es in
    let concl =
      f_equivS (snd es.dces_ml) (snd es.dces_mr) pr
        (s_cat es.dces_rl es.dces_cl) (s_cat es.dces_rr es.dces_cr) po
    in
    FApi.xmutate1 tc `Undelay [concl]

  let t_dcEquivS_undelay = FApi.t_low0 "dcEquivS-undelay" t_dcEquivS_undelay_r

  (* dcEquivF with empty R/S -> equivF *)
  let t_dcEquivF_undelay_r tc =
    let ef = tc1_as_dcEquivF tc in
    let empty s = List.is_empty s.EcAst.s_node in
    if not (empty ef.dcef_rl) then
      tc_error !!tc ~who:"undelay" "left delay context R1 is not empty";
    if not (empty ef.dcef_rr) then
      tc_error !!tc ~who:"undelay" "right delay context R2 is not empty";
    if not (empty ef.dcef_sl) then
      tc_error !!tc ~who:"undelay" "left continuation S1 is not empty";
    if not (empty ef.dcef_sr) then
      tc_error !!tc ~who:"undelay" "right continuation S2 is not empty";
    let pr = dcef_pr ef in
    let po = dcef_po ef in
    let concl = f_equivF pr ef.dcef_fl ef.dcef_fr po in
    FApi.xmutate1 tc `Undelay [concl]

  let t_dcEquivF_undelay = FApi.t_low0 "dcEquivF-undelay" t_dcEquivF_undelay_r
end

(* -------------------------------------------------------------------- *)
let t_delay tc =
  let concl = FApi.tc1_goal tc in
  match concl.f_node with
  | FequivS _ -> LowInternal.t_equivS_delay tc
  | FequivF _ -> LowInternal.t_equivF_delay tc
  | _ ->
      tc_error_noXhl
        ~kinds:[`Equiv `Any] !!tc

(* -------------------------------------------------------------------- *)
let t_undelay tc =
  let concl = FApi.tc1_goal tc in
  match concl.f_node with
  | FdcEquivS _ -> LowInternal.t_dcEquivS_undelay tc
  | FdcEquivF _ -> LowInternal.t_dcEquivF_undelay tc
  | _ ->
      tc_error_noXhl
        ~kinds:[`DCoupl `Any] !!tc
