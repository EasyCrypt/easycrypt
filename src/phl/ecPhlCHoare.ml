open EcUtils
open EcPath
open EcFol
open EcEnv
open EcMaps
open EcCoreGoal
open EcModules

(* ------------------------------------------------------------------ *)
(* Instantiation of [mi] by [marg] in [f].
   Precondition: [mp_arg] and [mi] types must be compatible. *)
let choare_modapply_args
    tc (mi : EcIdent.t) (mp_arg : mpath) (f : form) apply_info =
  let env = FApi.tc1_env tc in

  (* We look for procedures of [mi] used in [f]. *)
  let mi_procs = ref Sstr.empty in

  let is_instantiated fn =
    (* Sanity check *)
    assert (fn.x_top.m_args = []);
    let id = EcPath.mget_ident fn.x_top in
    EcIdent.id_equal id mi in

  let add_el fn _ =
    if is_instantiated fn then
      mi_procs := Sstr.add fn.x_sub !mi_procs in

  let rec doit f =
    let () = match f.f_node with
      | FcHoareF choare ->
        Mx.iter add_el choare.chf_co.c_calls
      | FcHoareS choare ->
        Mx.iter add_el choare.chs_co.c_calls
      | _ -> () in
    f_iter doit f in

  doit f;

  (* All procedures for which a choare must be provided in the module
     application. *)
  let mi_procs = !mi_procs in

  (* Compute the new cost after instantiating [mi] in [cost], provided
     [mi]'s procedures have costs [mi_costs]. *)
  let comp_cost (mi_costs : (xpath * cost) list) (cost : cost) =
    (* Subset of [mi_procs] appearing in [cost]. *)
    let procs_to_inst = Mx.fold (fun fn _ procs ->
        if is_instantiated fn then fn :: procs else procs
      ) cost.c_calls [] in

    (* We remove from cost the oracle calls we instantiate. *)
    let c_calls = Mx.filter (fun fn _ ->
        not (is_instantiated fn)) cost.c_calls in
    let cost' = cost_r cost.c_self c_calls in

    (* We compute the new cost. *)
    List.fold_left (fun cost' fn_to_inst ->
        let proc_cost = List.assoc fn_to_inst mi_costs in
        cost_op (fun f1 f2 ->
            let nb_calls = Mx.find fn_to_inst cost.c_calls in
            f_int_add_simpl f1 (f_int_mul_simpl nb_calls f2)
          ) cost' proc_cost
      ) cost' procs_to_inst in

  (* We compute the new module parameters, in case [mi] is a functor. *)
  let mp = EcPath.mident mi in
  let me = EcEnv.Mod.by_mpath mp env in
  let restr = EcEnv.NormMp.get_restr_me env me mp in

  let s_params = List.map (fun (id, mt) ->
      id, (EcIdent.fresh id, mt)
    ) me.me_params in
  let bindings = List.map (fun (_, (fid, mt)) ->
      fid, GTmodty mt
    ) s_params in

  (* Application of the argument [mp_arg] on its parameters. *)
  let mp_arg_app =
    EcPath.m_apply mp_arg (List.map (fun id -> EcPath.mident (fst id)) bindings) in

  (* Compute the choare hypothesis for [marg_app]'s procedure [fn]. *)
  let mk_hyp fn info =
    (* xpath of the function after substitution. *)
    let xfn = EcPath.xpath mp_arg_app fn in
    (* oracle path (i.e. with empty module arguments) of [fn] in [mi]. *)
    let xfn_in_mi = EcPath.xpath mp fn in
    (* Oracle restriction on [fn] in [mi]. *)
    let oi = EcSymbols.Msym.find fn restr.mr_oinfos in

    (* We process info, which let the user provide:
       - the self cost.
       - the number of calls to oracles that are not in [me_arg] params. *)
    let cost = EcProofTyping.tc1_process_cost tc EcTypes.tint info in
    let c_self  = cost.c_self in
    let c_calls = cost.c_calls in

    (* For oracles that are in params, we use corresponding entry in [restr]. *)
    let c_calls = Mx.fold (fun o obd c_calls ->
        (* We compute the name of the procedure, seen as an oracle of [mp_arg] *)
        let omod, ofun = EcPath.mget_ident o.x_top, o.x_sub in
        let omod = fst (List.assoc omod s_params) in
        let o = EcPath.xpath (EcPath.mident omod) ofun in
        Mx.add o obd c_calls
      ) (OI.costs oi) c_calls in

    let cost = cost_r c_self c_calls in
    let choare = f_cHoareF f_true xfn f_true cost in
    (xfn_in_mi, choare) in

  let procs_todo, hyps_assoc = List.fold_left (fun (procs_todo, hyps) (fn, info) ->
      if not (Sstr.mem fn mi_procs) then
        tc_error !!tc "choare apply: procedure %s is provided, but is not \
                       used" fn;

      if not (Sstr.mem fn procs_todo) then
        tc_error !!tc "choare apply: procedure %s is provided twice" fn;
      let procs_todo = Sstr.remove fn procs_todo in

      let new_hyp = mk_hyp fn info in

      (procs_todo, new_hyp :: hyps)
    ) (mi_procs, [])  apply_info in

  if not (Sstr.is_empty procs_todo) then begin
    let l = Sstr.elements procs_todo in
    tc_error !!tc "@[<v 2>choare_apply: no costs have been provided for %s's \
                   procedures:@;\
                   %a@]"
      (EcIdent.name mi)
      (EcPrinting.pp_list ", " Format.pp_print_string) l end;

  let hyps = List.map snd hyps_assoc in

  (* We update all costs in [f], by removing [mi]'s procedures. *)
  let mi_procs = List.map (fun (x,ch) -> match ch.f_node with
      | FcHoareF ch -> x, ch.chf_co
      | _ -> assert false ) hyps_assoc in
  let tx _ f_new = match f_new.f_node with
    | FcHoareF ch ->
      let ch = { ch with chf_co = comp_cost mi_procs ch.chf_co } in
      f_cHoareF_r ch
    | FcHoareS ch ->
      let ch = { ch with chs_co = comp_cost mi_procs ch.chs_co } in
      f_cHoareS_r ch
    | _ -> f_new in

  let f = Fsubst.f_subst ~tx Fsubst.f_subst_id f in

  let fs = Fsubst.f_bind_mod Fsubst.f_subst_id mi mp_arg_app in
  let f = Fsubst.f_subst fs f in

  f_forall bindings (f_imps hyps f)
