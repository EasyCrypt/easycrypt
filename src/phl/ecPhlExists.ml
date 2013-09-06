(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcCorePhl
open EcCoreHiLogic

(* -------------------------------------------------------------------- *)
class rn_hl_exists_elim = object
  inherit xrule "[hl] elim-exists"
end

let rn_hl_exists_elim = RN_xtd (new rn_hl_exists_elim :> xrule)

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  let get_to_gen side f = 
    let do_side m = 
      match side with
      | true  when EcIdent.id_equal m mleft  -> true
      | true  when EcIdent.id_equal m mright -> false
      | false when EcIdent.id_equal m mhr    -> true
      | _ -> assert false
    in
      match f.f_node with
      | Fpvar(pv, m) -> 
          let id = id_of_pv pv m in
            (id, do_side m, f_pvar pv f.f_ty, f)

      | Fglob(mp, m) ->
          let id = id_of_mp mp m in
            (id, do_side m, f_glob mp, f)

      | _ -> tacuerror "global memory or variable expected"

  let get_to_gens side fs = 
    List.map (get_to_gen side) fs
end

(* -------------------------------------------------------------------- *)
let t_hr_exists_elim g = 
  let concl = get_concl g in
  let pre = get_pre concl in
  let bd, pre = destr_exists pre in
  (* TODO check that bd is not bind in the post *)
  let concl = f_forall bd (set_pre ~pre concl) in
    prove_goal_by [concl] rn_hl_exists_elim g

let t_hr_exists_intro fs g = 
  let hyps, concl = get_goal g in 
  let pre = get_pre concl in
  let post = get_post concl in
  let side = is_equivS concl || is_equivF concl in
  let gen = LowInternal.get_to_gens side fs in
  let eqs = List.map (fun (id,_,_,f) -> f_eq (f_local id f.f_ty) f) gen in
  let bd = List.map (fun (id,_,_,f) -> id, GTty f.f_ty) gen in
  let pre = f_exists bd (f_and (f_ands eqs) pre) in
  let ms = 
    if   side
    then LDecl.fresh_ids hyps ["&ml";"&mr";"H"] 
    else LDecl.fresh_ids hyps ["&m";"H"] in
  let h = List.hd (List.rev ms) in
  let args = 
    let ml = List.hd ms in
    let mr = if side then List.hd (List.tl ms) else ml in
    let do1 (_, side, mk, _) = AAform (mk (if side then ml else mr)) in
      List.map do1 gen
  in
    t_seq_subgoal (EcPhlConseq.t_conseq pre post)
      [t_lseq [t_intros_i ms;
               gen_t_exists (fun _ _ f -> f) args; 
               t_hyp h];
       t_trivial; t_id None]
      g

(* -------------------------------------------------------------------- *)
let process_exists_intro fs g = 
  let hyps,concl = get_goal g in
  let penv = 
    match concl.f_node with
    | FhoareF hf -> fst (LDecl.hoareF hf.hf_f hyps)
    | FhoareS hs -> LDecl.push_active hs.hs_m hyps 
    | FbdHoareF bhf ->fst (LDecl.hoareF bhf.bhf_f hyps) 
    | FbdHoareS bhs -> LDecl.push_active bhs.bhs_m hyps 
    | FequivF ef -> fst (LDecl.equivF ef.ef_fl ef.ef_fr hyps)
    | FequivS es -> LDecl.push_all [es.es_ml; es.es_mr] hyps 
    | _ -> tacuerror "cannot apply conseq rule, not a phl/prhl judgement"
  in

  let fs = List.map (fun f -> process_form_opt penv f None) fs in
    t_hr_exists_intro fs g 
