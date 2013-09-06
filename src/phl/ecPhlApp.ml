(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcTypes
open EcModules
open EcFol
open EcParsetree
open EcBaseLogic
open EcLogic
open EcCorePhl
open EcCoreHiPhl


(* BdHoare App
 *    {P}c1{phi}
 *    {P}c1{R} ? f1
 *    {phi /\ R}c2{Q} ? f2
 *    {P}c1{!R} ? g1
 *    {phi /\ !R}c2{Q} ? g2
 * =====================================
 *    {P}c1;c2{Q} ? f1 * f2 + g1 * g2
 *)

(* -------------------------------------------------------------------- *)
class rn_hl_append td (dp : int doption) phi bdi =
object
  inherit xrule "[hl] append"

  method tacdir  : tac_dir     = td
  method doption : int doption = dp
  method phi     : form        = phi
  method bdi     : app_bd_info = bdi
end

let rn_hl_append td dp phi bdi =
  RN_xtd (new rn_hl_append td dp phi bdi :> xrule)

(* -------------------------------------------------------------------- *)
let t_hoare_app i phi g =
  let concl = get_concl g in
  let hs = t_as_hoareS concl in
  let s1,s2 = s_split "app" i hs.hs_s in
  let a = f_hoareS_r { hs with hs_s = stmt s1; hs_po = phi }  in
  let b = f_hoareS_r { hs with hs_pr = phi; hs_s = stmt s2 } in
    prove_goal_by [a;b] (rn_hl_append Backs (Single i) phi AppNone) g

let t_bdHoare_app i (phi,pR,f1,f2,g1,g2) g =
  let concl = get_concl g in
  let bhs = t_as_bdHoareS concl in
  let s1,s2 = s_split "app" i bhs.bhs_s in
  let s1, s2 = stmt s1, stmt s2 in
  let nR = f_not pR in
  let cond_phi = f_hoareS bhs.bhs_m bhs.bhs_pr s1 phi in
  let condf1 = f_bdHoareS_r { bhs with bhs_s = s1; bhs_po = pR; bhs_bd=f1} in
  let condg1 = f_bdHoareS_r { bhs with bhs_s = s1; bhs_po = nR; bhs_bd=g1} in
  let condf2 = f_bdHoareS_r
    { bhs with bhs_s = s2; bhs_pr = f_and_simpl phi pR;bhs_bd=f2} in
  let condg2 = f_bdHoareS_r
    { bhs with bhs_s = s2; bhs_pr = f_and_simpl phi nR;bhs_bd=g2} in
  let (m0,m0ty) = bhs.bhs_m in
  let mt = EcIdent.fresh m0 in
  let mf = EcIdent.fresh m0 in
  let m0mt = Fsubst.f_subst_mem m0 mt in
  let m0mf = Fsubst.f_subst_mem m0 mf in
  let bd =
    let f2 = m0mt f2 in
    let g2 = m0mf g2 in
    (f_real_add_simpl (f_real_prod_simpl f1 f2) (f_real_prod_simpl g1 g2)) in
  let condbd =
    match bhs.bhs_cmp with
    | FHle -> f_real_le bd bhs.bhs_bd
    | FHeq -> f_eq bd bhs.bhs_bd
    | FHge -> f_real_le bhs.bhs_bd bd in
  let condbd =
    f_imps [bhs.bhs_pr; m0mt pR; m0mt phi; m0mf nR; m0mf phi] condbd in
  let conds = [ f_forall_mems [bhs.bhs_m; (mt,m0ty); (mf,m0ty)] condbd ] in
  let conds =
    if f_equal g1 f_r0 then condg1 :: conds
    else if f_equal g2 f_r0 then condg2 :: conds
    else condg1 :: condg2 :: conds in
  let conds =
    if f_equal f1 f_r0 then condf1 :: conds
    else if f_equal f2 f_r0 then condf2 :: conds
    else condf1 :: condf2 :: conds in
  let conds = cond_phi :: conds in
    (* FIXME: the attached information is meaningless *)
    prove_goal_by conds (rn_hl_append Backs (Single i) pR AppNone) g

let t_equiv_app (i,j) phi g =
  let concl = get_concl g in
  let es = t_as_equivS concl in
  let sl1,sl2 = s_split "app" i es.es_sl in
  let sr1,sr2 = s_split "app" j es.es_sr in
  let a = f_equivS_r {es with es_sl=stmt sl1; es_sr=stmt sr1; es_po=phi} in
  let b = f_equivS_r {es with es_pr=phi; es_sl=stmt sl2; es_sr=stmt sr2} in
    prove_goal_by [a;b] (rn_hl_append Backs (Double (i, j)) phi AppNone) g

(* -------------------------------------------------------------------- *)
let process_phl_bd_info dir g bd_info =
  match bd_info with
  | PAppNone ->
      let hs = t_as_bdHoareS (get_concl g) in
      let f1, f2 =
         match dir with
        | Backs -> hs.bhs_bd, f_r1
        | Fwds  -> f_r1, hs.bhs_bd
  
      in
        (* The last argument will not be used *)
        (f_true, f1, f2, f_r0, f_r1)

  | PAppSingle f ->
      let f = process_phl_formula g f in
      let hs = t_as_bdHoareS (get_concl g) in
      let f1, f2 =
        match dir with
        | Backs  -> f_real_div hs.bhs_bd f, f
        | Fwds   -> f, f_real_div hs.bhs_bd f
      in
        (f_true, f1, f2, f_r0, f_r1)

  | PAppMult (phi,f1,f2,g1,g2) ->
      let phi = phi |> omap_dfl (process_phl_formula g) f_true in
      let check_0 f =
        if not (f_equal f f_r0) then
          tacuerror "the formula should be 0%%r" in
      let process_f (f1,f2) =
        match f1, f2 with
        | None, None ->
            (* Not accepted by the parser *)
            assert false

        | Some f, None ->
          let loc = f.pl_loc in
          let f = process_phl_form treal g f in
            set_loc loc check_0 f;
            (f, f_r1)

        | None, Some f ->
          let loc = f.pl_loc in
          let f = process_phl_form treal g f in
          set_loc loc check_0 f;
            (f_r1, f)

        | Some f1, Some f2 ->
            (process_phl_form treal g f1, process_phl_form treal g f2)
    in

    let f1, f2 = process_f (f1, f2) in
    let g1, g2 = process_f (g1, g2) in
      (phi, f1, f2, g1, g2)

(* -------------------------------------------------------------------- *)
let process_app dir k phi bd_info g =
  let concl = get_concl g in

  match k, bd_info with
  | Single i, PAppNone when is_hoareS concl ->
      let phi = process_phl_formula g phi in
        t_hoare_app i phi g

  | Single i, _ when is_bdHoareS concl ->
      let pR = process_phl_formula g phi in
      let (phi,f1,f2,f3,f4) = process_phl_bd_info dir g bd_info in
        t_bdHoare_app i (phi, pR, f1, f2, f3, f4) g

  | Double(i,j), PAppNone ->
    let phi = process_prhl_formula g phi in
      t_equiv_app (i, j) phi g

  | Single _, PAppNone ->
      cannot_apply "app" "wrong position parameter"

  | _, _ ->
      cannot_apply "app" "optional bound parameter not supported"
