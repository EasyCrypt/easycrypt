(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcEnv

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  let get_to_gen pf side f =
    let do_side m =
      match side with
      | true  when EcIdent.id_equal m mleft  -> true
      | true  when EcIdent.id_equal m mright -> false
      | false when EcIdent.id_equal m mhr    -> true
      | _ -> assert false
    in
      match f.f_node with
      | Fpvar (pv, m) ->
          let id = id_of_pv pv m in
            (id, do_side m, f_pvar pv f.f_ty, f)

      | Fglob (mp, m) ->
          let id = id_of_mp mp m in
            (id, do_side m, f_glob mp, f)

      | _ -> tc_error pf "global memory or variable expected"

  let get_to_gens pf side fs =
    List.map (get_to_gen pf side) fs
end

(* -------------------------------------------------------------------- *)
let t_hr_exists_elim_r tc =
  let pre = tc1_get_pre tc in
  let bd, pre = destr_exists_prenex pre in
  (* FIXME: check that bd is not bound in the post *)
  let concl = f_forall bd (set_pre ~pre (FApi.tc1_goal tc)) in
  FApi.xmutate1 tc `HlExists [concl]

(* -------------------------------------------------------------------- *)
let t_hr_exists_intro_r fs tc =
  let hyps  = FApi.tc1_hyps tc in
  let concl = FApi.tc1_goal tc in
  let pre   = tc1_get_pre  tc in
  let post  = tc1_get_post tc in
  let side  = is_equivS concl || is_equivF concl in
  let gen   = LowInternal.get_to_gens !!tc side fs in
  let eqs   = List.map (fun (id, _, _, f) -> f_eq (f_local id f.f_ty) f) gen in
  let bd    = List.map (fun (id, _, _, f) -> (id, GTty f.f_ty)) gen in
  let pre   = f_exists bd (f_and (f_ands eqs) pre) in

  let h = LDecl.fresh_id hyps "h" in
  let ms, (ml, mr) =
    match side with
    | true ->
        let ml, mr = as_seq2 (LDecl.fresh_ids hyps ["&ml"; "&mr"]) in
        ([ml; mr], (ml, mr))

    | false ->
        let m = LDecl.fresh_id hyps "&m" in ([m], (m, m))
  in

  let args =
    let do1 (_, side, mk, _) = PAFormula (mk (if side then ml else mr)) in
    List.map do1 gen
  in

  let tactic =
    FApi.t_seqsub (EcPhlConseq.t_conseq pre post)
      [ FApi.t_seqs [
          t_intros_i (ms@[h]);
          t_exists_intro_s args;
          t_apply_hyp h;
        ];
        t_logic_trivial;
        t_id]
  in
  FApi.t_internal tactic tc

(* -------------------------------------------------------------------- *)
let t_hr_exists_elim  = FApi.t_low0 "hr-exists-elim"  t_hr_exists_elim_r
let t_hr_exists_intro = FApi.t_low1 "hr-exists-intro" t_hr_exists_intro_r

(* -------------------------------------------------------------------- *)
let process_exists_intro fs tc =
  let (hyps, concl) = FApi.tc1_flat tc in
  let penv =
    match concl.f_node with
    | FhoareF hf -> fst (LDecl.hoareF hf.hf_f hyps)
    | FhoareS hs -> LDecl.push_active hs.hs_m hyps
    | FbdHoareF bhf -> fst (LDecl.hoareF bhf.bhf_f hyps)
    | FbdHoareS bhs -> LDecl.push_active bhs.bhs_m hyps
    | FequivF ef -> fst (LDecl.equivF ef.ef_fl ef.ef_fr hyps)
    | FequivS es -> LDecl.push_all [es.es_ml; es.es_mr] hyps
    | _ -> tc_error_notphl !!tc None    (* FIXME *)
  in

  let fs =
    List.map
      (fun f -> TTC.pf_process_form_opt !!tc penv None f)
      fs
  in
    t_hr_exists_intro fs tc
