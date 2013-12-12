(* -------------------------------------------------------------------- *)
open EcModules
open EcFol
open EcBaseLogic
open EcLogic
open EcCorePhl

(* -------------------------------------------------------------------- *)
class rn_hl_rcond side br pos =
object
  inherit xrule "[hl] rcond"

  method side     : bool option = side
  method branch   : bool        = br
  method position : int         = pos
end

let rn_hl_rcond side br pos =
  RN_xtd (new rn_hl_rcond side br pos :> xrule)

(* -------------------------------------------------------------------- *)
module Low = struct
  let gen_rcond b m at_pos s =
    let head, i, tail = s_split_i "rcond" at_pos s in 
    let e, s = 
      match i.i_node with
      | Sif(e,s1,s2) -> e, if b then s1.s_node else s2.s_node
      | Swhile(e,s1) -> e, if b then s1.s_node@[i] else [] 
      | _ -> 
        cannot_apply "rcond" 
          (Format.sprintf "the %ith instruction is not a conditionnal" at_pos) in
    let e = form_of_expr m e in
    let e = if b then e else f_not e in
    stmt head, e, stmt (head@s@tail)
    
  let t_hoare_rcond b at_pos g = 
    (* FIXME: generalize the rule using assume *)
    let concl = get_concl g in
    let hs = t_as_hoareS concl in
    let m  = EcMemory.memory hs.hs_m in 
    let hd,e,s = gen_rcond b m at_pos hs.hs_s in
    let concl1  = f_hoareS_r { hs with hs_s = hd; hs_po = e } in
    let concl2  = f_hoareS_r { hs with hs_s = s } in
    prove_goal_by [concl1;concl2] (rn_hl_rcond None b (at_pos)) g  
  
  let t_bdHoare_rcond b at_pos g = 
    let concl = get_concl g in
    let bhs = t_as_bdHoareS concl in
    let m  = EcMemory.memory bhs.bhs_m in 
    let hd,e,s = gen_rcond b m at_pos bhs.bhs_s in
    let concl1  = f_hoareS bhs.bhs_m bhs.bhs_pr hd e in
    let concl2  = f_bdHoareS_r { bhs with bhs_s = s } in
    prove_goal_by [concl1;concl2] (rn_hl_rcond None b (at_pos)) g  
  
  let t_equiv_rcond side b at_pos g =
    let concl = get_concl g in
    let es = t_as_equivS concl in
    let m,mo,s = 
      if side then es.es_ml,es.es_mr, es.es_sl 
      else         es.es_mr,es.es_ml, es.es_sr in
    let hd,e,s = gen_rcond b EcFol.mhr at_pos s in 
    let mo' = EcIdent.create "&m" in
    let s1 = 
      Fsubst.f_bind_mem 
        (Fsubst.f_bind_mem Fsubst.f_subst_id (EcMemory.memory m) EcFol.mhr)
        (EcMemory.memory mo) mo' in
    let pre1  = Fsubst.f_subst s1 es.es_pr in
    let concl1 = 
      f_forall_mems [mo', EcMemory.memtype mo] 
        (f_hoareS (EcFol.mhr, EcMemory.memtype m) pre1 hd e) in
    let sl,sr = if side then s, es.es_sr else es.es_sl, s in
    let concl2 = f_equivS_r { es with es_sl = sl; es_sr = sr } in
    prove_goal_by [concl1;concl2] (rn_hl_rcond (Some side) b (at_pos)) g 
end

(* -------------------------------------------------------------------- *)
let t_rcond side b at_pos g =
  let concl = get_concl g in
    match side with
    | None when is_bdHoareS concl -> Low.t_bdHoare_rcond b at_pos g
    | None -> Low.t_hoare_rcond b at_pos g
    | Some side -> Low.t_equiv_rcond side b at_pos g
